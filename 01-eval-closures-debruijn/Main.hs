
module Main where

import Prelude hiding (lookup, length, even)
import qualified Prelude (length)
import Control.Applicative hiding (many, some)
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Data.Char

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

data Tm
  = Var Ix
  | Lam Tm      -- lam (x.t)
  | App Tm Tm
  | Let Tm Tm   -- let t (x.u)

data Env
  = Nil
  | Define Env ~Val   -- list of lazy value

data Closure
  = Closure Env Tm

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam {-# unpack #-} Closure

--------------------------------------------------------------------------------

length :: Env -> Lvl
length = go 0 where
  go acc Nil            = acc
  go acc (Define env _) = go (acc + 1) env

lookup :: Env -> Ix -> Val
lookup (Define env v) 0 = v
lookup (Define env _) x = lookup env (x - 1)
lookup _              _ = error "index out of scope"

cApp :: Closure -> Val -> Val
cApp (Closure env t) ~u = eval (Define env u) t

eval :: Env -> Tm -> Val
eval env = \case
  Var x   -> lookup env x
  App t u -> case (eval env t, eval env u) of  -- eval-apply
               (VLam t, u) -> cApp t u
               (t     , u) -> VApp t u
  Lam t   -> VLam (Closure env t)
  Let t u -> eval (Define env (eval env t)) u

-- Normalization
--------------------------------------------------------------------------------

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Val -> Tm              -- normalization-by-evaulation
quote l = \case
  VVar x   -> Var (lvl2Ix l x)
  VApp t u -> App (quote l t) (quote l u)
  VLam t   -> Lam (quote (l + 1) (cApp t (VVar l)))

nf :: Env -> Tm -> Tm
nf env t = quote (length env) (eval env t)

-- ("\\" works for lambda as well)
ex = main' "nf" $ unlines [
  "let λ λ 1 (1 (1 (1 (1 0))));",    -- five = λ s z. s (s (s (s (s z))))
  "let λ λ λ λ 3 1 (2 1 0);",        -- add  = λ a b s z. a s (b s z)
  "let λ λ λ λ 3 (2 1) 0;",          -- mul  = λ a b s z. a (b s) z
  "let 1 2 2;",                      -- ten  = add five five
  "let 1 0 0;",                      -- hundred = mul ten ten
  "let 2 1 0;",                      -- thousand = mul ten hundred
  "0"                                -- thousand
  ]

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isDigit *> empty) <|> ws

pIx    = lexeme L.decimal
pAtom  = (Var <$> pIx) <|> parens pTm
pSpine = foldl1 App <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  Lam <$> pTm

pLet = do
  pKeyword "let"
  t <- pTm
  pKeyword ";"
  u <- pTm
  pure $ Let t u

pTm  = pLam <|> pLet <|> pSpine
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO Tm
parseStdin = parseString =<< getContents

-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where
  goArg = go True

  goLam (Lam t) = ("λ "++) . goLam t
  goLam t       = go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x            -> (show x++)
    App (App t u) u' -> showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')
    App t u          -> showParen p (go True t . (' ':) . goArg u)
    Lam t            -> showParen p (("λ "++) . goLam t)
    Let t u          -> ("let "++) . go False t . ("\n;\n"++) . go False u

instance Show Tm where showsPrec = prettyTm


-- main
--------------------------------------------------------------------------------

var = Var
lam = Lam
app = App
infixl 4 `app` 

-- Church numeral of 3
c3 :: Tm
c3 = Lam (Lam (Var 1 `app` (Var 1 `app` (Var 1 `app` Var 0))))
--c3 = lam (\f -> lam (\x -> var f `app` (var f `app` (var f `app` var x))))

cadd :: Tm
cadd = Lam (Lam (Lam (Lam ( 
          Var 3 `app` Var 1 
            `app` (Var 2 `app` Var 1 `app` Var 0)))))

--cadd = lam (\n -> lam (\m -> lam (\f -> lam (\x -> 
--          var n `app` var f 
--            `app` (var m `app` var f `app` var x)))))

t3 :: Tm
t3 = cadd `app` c3 `app` c3

-- printLam (norm t3)
-- (λ x1. (λ x2. x1 x1 x1 x1 x1 x1 x2))

cmul :: Tm
cmul = lam (lam (lam (lam ( 
         var 3 `app` (var 2 `app` var 1) `app` var 0))))

t4 :: Tm
t4 = cmul `app` t3 `app` t3

t5 :: Tm
t5 = cmul `app` t4 `app` t4

t6 :: Tm
t6 = cmul `app` t4 `app` t5

t7 :: Tm
t7 = cmul `app` t5 `app` t4

t8 :: Tm
t8 = cmul `app` t6 `app` t3


cnum :: Int -> Tm
cnum n = lam (lam (go n)) where
  go 0 = var 0
  go n = var 1 `app` (go (n - 1))

-- \x y . x
tt :: Tm
tt = lam (lam (var 1))

-- \x y . y
ff :: Tm
ff = lam (lam (var 0))


-- \b x y . b y x
neg :: Tm
neg = lam (lam (lam ((var 2 `app` var 0) `app` var 1)))

-- \b c x y . b (c x y) y
cand :: Tm
cand = lam (lam (lam (lam ((var 3 `app` (var 2 `app` var 1 `app` var 0)) `app` var 0))))

-- \n . n neg tt 
even :: Tm 
even = lam ((var 0 `app` neg) `app` tt)


-- NbE is slow on this term: normalising this term is quadratic wrt to the number 50000
-- in this term because `f` is re-normalised in every function call.
t10 :: Tm
t10 = cnum 50000 `app` (lam (cand `app` (f `app` var 0) `app` var 0)) `app` tt where
  expensive = even `app` (cnum 50000)
  f = lam expensive


badShow :: Tm -> String 
badShow (Var x) = show x
badShow (App x y) = badShow x ++ " " ++ badShow y
badShow (Lam body) = "(λ " ++ show ". " ++ badShow body ++ ")"

main :: IO ()
main = print (nf Nil t10)

helpMsg = unlines [
  "usage: elabzoo-eval [--help|nf]",
  "  --help : display this message",
  "  nf     : read expression from stdin, print its normal form"]

mainWith :: IO [String] -> IO Tm -> IO ()
mainWith getOpt getTm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]     -> print . nf Nil  =<< getTm
    _          -> putStrLn helpMsg

--main :: IO ()
--main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
