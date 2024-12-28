{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE GADTs #-}

module Main where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (ap, guard)
import qualified Text.ParserCombinators.ReadP as ReadP
import Text.Read hiding (step)
import qualified Text.Read.Lex as Read
import qualified Text.Read as Read
import Data.Char hiding (Control)
import Data.Foldable

data Event = App1 | App2 | Let1 | Let2 | NewPrompt Tag | Capture Tag | Jump Cntr deriving Show

type Name = String
type Tag = String
data Exp
  = Var Name
  | Lit Integer
  | Lam Name Exp
  | App Exp Exp
  | Prompt Tag Exp
  | Control Tag Name Exp

class Trace d where
  step :: Event -> d -> d

class Domain d where
  stuck :: d
  lit :: Integer -> d
  fun :: (d -> d) -> d
  app :: d -> d -> d
  delim :: ((((d -> d) -> d) -> d) -> d) -> d

eval :: (Trace d, Domain d) => Exp -> Map Name d -> Map Tag (((d -> d) -> d) -> d) -> d
eval e names tags = case e of
  Lit n -> lit n
  Var x | Just d <- Map.lookup x names -> d
        | otherwise                    -> stuck
  Lam x e -> fun (\v -> step App2 (eval e (Map.insert x v names) tags))
  App f a -> step App1 (app (eval f names tags) (eval a names tags))
  Prompt tag e -> delim (\control -> step (NewPrompt tag) (eval e names (Map.insert tag control tags)))
  Control tag x e | Just control <- Map.lookup tag tags -> control (\k -> step (Capture tag) (eval e (Map.insert x (fun k) names) tags))
                | otherwise                         -> stuck

data T a = Step Event (T a) | Ret !a deriving Functor
instance Trace (T a) where step = Step
instance Applicative T where pure = Ret; (<*>) = ap
instance Monad T where Step ev t >>= k = Step ev (t >>= k); Ret v >>= k = k v

type Cntr = Int

type Stack = [(Cntr, Value -> T Value)]
type C = Stack -> T Value
data Value = Nat Integer | Fun (C -> C) | Stuck

instance Trace C where
  step ev c ks = step ev (c ks)

instance Domain C where
  stuck _ = return Stuck
  lit n = contract (Nat n)
  fun f = contract (Fun f)
  app d a ks = d $ push ks (\v -> case v of
    Fun f -> a $ push ks (\v -> f (contract v) ks)
    _ -> return Stuck)
  delim f k = f control k1
    where (cnt, k1) = newPrompt k
          control f k | Just (pref,suff) <- splitStack cnt k = f (\d k -> step (Jump cnt) d (pref ++ k)) suff
                      | otherwise                            = return Stuck

push :: Stack -> (Value -> T Value) -> Stack
push [] f     = push [(0, return)] f
push ((c,_):ks) f = (c,f) : ks

newPrompt :: Stack -> (Cntr, Stack)
newPrompt [] = newPrompt [(0, return)]
newPrompt ks@((c,_):_) = (c, (c+1,return):ks)

splitStack :: Cntr -> Stack -> Maybe (Stack, Stack)
splitStack c = go []
  where
    go pref suff@((c',_):_) | c == c' = if null pref then Nothing else Just (reverse pref, suff)
    go pref (frame:suff) = go (frame:pref) suff
    go _    []           = Nothing

dropTail :: Int -> [a] -> [a]
dropTail n = reverse . drop n . reverse

contract :: Value -> C
contract v [] = return v
contract v ((_c,k):ks) = k v >>= \v -> contract v ks

evalTop :: Exp -> T Value
evalTop e = eval e topenv Map.empty ([] :: Stack)
  where
    topenv = Map.fromList
      [ ("inc", fun (\d ks -> d $ push ks (\v -> case v of Nat n -> return (Nat (n+1)); _ -> return Stuck)))
      ]

instance Show Value where
  show Stuck = "stuck"
  show (Fun _) = "fun"
  show (Nat n) = show n
instance Show v => Show (T v) where
  show (Step ev t) = show ev ++ "->" ++ show t
  show (Ret v) = show v

main :: IO ()
main = do
  print $ evalTop (read "let i = λx.x in i i")
  print $ evalTop (read "prompt tag (inc (control tag k (k (k 0))))")
  print $ evalTop (read "let i = λx.x in prompt tag (i (control tag k (k (k i))))")

appPrec, lamPrec, varPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1
varPrec = appPrec+1

instance Show Exp where
  showsPrec _ (Lit n)      = shows n
  showsPrec _ (Var v)      = showString v
  showsPrec p (App f arg)  = showParen (p > appPrec) $
    showsPrec appPrec f . showString " " . showsPrec varPrec arg
  showsPrec p (Lam b body) = showParen (p > lamPrec) $
    showString "λ" . showString b . showString ". " . showsPrec lamPrec body
  showsPrec p (Control tag x e) = showParen (p > lamPrec) $
    showString "control "
    . showString tag
    . showString " "
    . showString x
    . showString " "
    . showsPrec varPrec e
  showsPrec p (Prompt tag e) = showParen (p > lamPrec) $
    showString "prompt "
    . showString tag
    . showString " "
    . showsPrec varPrec e

showSep :: ShowS -> [ShowS] -> ShowS
showSep _   [] = id
showSep _   [s] = s
showSep sep (s:ss) = s . sep . showString " " . showSep sep ss

-- | The default 'ReadP.many1' function leads to ambiguity. What a terrible API.
greedyMany, greedyMany1 :: ReadP.ReadP a -> ReadP.ReadP [a]
greedyMany p  = greedyMany1 p ReadP.<++ pure []
greedyMany1 p = (:) <$> p <*> greedyMany p

-- | This monster parses Exprs in the REPL etc. It parses names that start
-- with an upper-case letter as literals and lower-case names as variables.
--
-- Accepts syntax like
-- @let x = λa. g z in (λb. j b) x@
--
-- >>> read "g z" :: Exp
-- g z
--
-- >>> read "λx.x" :: Exp
-- λx. x
--
-- >>> read "let x = x in x" :: Exp
-- let x = x in x
--
-- >>> read "let x = λa. g z in (λb. j b) x" :: Exp
-- let x = λa. g z in (λb. j b) x
--
-- >>> read "let x = λa. let y = y in a in g z" :: Exp
-- let x = λa. let y = y in a in g z
--
-- >>> read "let i = λx.x in prompt tag (i (control tag k (k (k i))))" :: Exp
instance Read Exp where
  readPrec = Read.parens $ Read.choice
    [ Var <$> readName
    , do
        Read.Number num <- Read.lexP
        Just n <- pure $ Read.numberToInteger num
        return (Lit n)
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        pure (foldl' App f args)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for Lam
        Var v <- Read.readPrec
        '.' <- Read.get
        Lam v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "let" <- Read.lexP
        x <- readName
        Read.Punc "=" <- Read.lexP
        e1 <- Read.readPrec
        Read.Ident "in" <- Read.lexP
        e2 <- Read.readPrec
        pure ((Lam x e2) `App` e1)
    , Read.prec lamPrec $ do
        Read.Ident "control" <- Read.lexP
        tag <- readName
        x <- readName
        e <- Read.readPrec
        pure (Control tag x e)
    , Read.prec lamPrec $ do
        Read.Ident "prompt" <- Read.lexP
        tag <- readName
        e <- Read.readPrec
        pure (Prompt tag e)
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in","case","of","control","prompt"])
        guard (not $ head v `elem` "λΛ@#5\\")
        guard (isLower $ head v) -- Ensures that there is no clash with ConTag
        guard (all isAlphaNum v)
        pure v
