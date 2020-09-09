-- Implement a logic programming environment as a DSL within purescript.
module Main where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer, fix)
import Data.Array (zipWith)
import Data.Foldable (foldr, intercalate)
import Data.Map.Internal (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Effect (Effect)
import Effect.Console (log)

data Term = Var Int
          | Compound String (Array Term)

instance showTerm :: Show Term where
    show (Var n) = "$" <> show n
    show (Compound atom list) = atom
      <> "(" <> intercalate ", " (map show list) <> ")"

-- Relates to Var Int, if the map is not containing the Variable,
--                     then it's a free variable.
--                     otherwise it is bound, and the value of the variable
--                                            is found in this map.
type State = { variableBindings :: Map Int Term
             , nextVariable     :: Int }

type Goal = State -> Array State


yes :: Goal -- prolog 'true'. -- 1, Equivalent to 'pure' in this context.
yes = \st -> [st]

no :: Goal -- prolog 'false'. -- 0
no = \st -> []

-- Creates a fresh variable
-- ∃x. ...
fresh :: (Term -> Goal) -> Goal
fresh f = \{variableBindings, nextVariable} ->
    f (Var nextVariable) -- nextVariable is free, so variableBindings stays intact.
      {variableBindings, nextVariable:nextVariable+1}

infix 5 conj as ∧ -- a * b
conj :: Goal -> Goal -> Goal
conj f g = \x -> f x >>= g


-- conj f g = \x -> combineResults <$> (f x) <*> (g x)
-- combineResults :: State -> State -> Array State -- kind of like union, but needs to unify terms too.

infix 4 disj as ∨ -- a + b
disj :: Goal -> Goal -> Goal
disj f g = \x -> f x <> g x

-- The result of reifyVar, is either a bound variable, or truly free variable.
--reifyVar :: Term -> State -> (t:Term ** NotIn t State)
reifyVar :: Term -> State -> Term -- produces a resulting term that is same value with input term
                                  -- and is verified to not be a bound variable.
reifyVar (Var i)        st = case lookup i st.variableBindings of
    Just v -> reifyVar v st
    Nothing -> (Var i)
reifyVar compound _ = compound

infix 6 eq as ≡
eq :: Term -> Term -> Goal
eq x y = \st -> unify (reifyVar x st) (reifyVar y st) st

-- Transforms the input state into state, where two input terms are the same.
-- To the unify, the bound input variables must be removed.

-- To unify two variables mean that they're the same value afterwards.
unify :: Term -> Term -> State -> Array State
unify (Var i)        (Var j)        st = -- these are free variables, so neither appears in the 'st'
    pure $ st {
                variableBindings = insert i (Var j) st.variableBindings }
unify (Var i)        compound       st = 
    pure $ st {
                variableBindings = insert i compound st.variableBindings }
unify compound       (Var j)        st =
    pure $ st { 
                variableBindings = insert j compound st.variableBindings }
unify (Compound n xs) (Compound m ys) st | (n == m) = let
    zzz = zipWith (\x y st -> unify (reifyVar x st) (reifyVar y st)) xs ys
    in foldr (>=>) pure zzz

unify (Compound n xs) (Compound m ys) st            = Nothing

--occurs :: Int -> Term -> State -> Boolean
--occurs i term st = ?occurs1

cons :: Term -> Term -> Term
cons x y = Compound "cons" [x, y]

nil :: Term
nil = Compound "nil" []

--list([]).
--list([X|R]) :- list(R).
listRule :: (Term -> Goal) -> Term -> Goal
listRule recFn xs = let
    rec = defer (\unit -> recFn)
    in (xs ≡ nil)
     ∨ (fresh $ \x -> fresh $ \r -> (xs ≡ cons x r ∧ rec r))
listR :: Term -> Goal
listR = fix listRule

example1 :: Goal
example1 = (fresh $ \x -> listR x) blank
-- [], [Y], ...


blank :: State
blank = {variableBindings : empty, nextVariable : 0}

--cat([], Result, Result) :- list(Result).
--cat([], [], []).
--cat([], [X|R], [X|R]).
--cat([X|Left], Right, [X|Result]) :-
--  cat(Left, Right, Result).

--snoc([], X, [X]).
--snoc([X|XS], Y, [X|YS]) :- snoc(XS, Y, YS).

--rev([],       []).
--rev([X|Left], Result) :-
--    rev(Left, Right),
--    snoc(Right, X, Result).

--nat(zero).
--nat(succ(X)) :- nat(X).

--balancedTree(leaf, zero).
--balancedTree(branch(X,Y), succ(N)) :-
    --balancedTree(X, N),
    --balancedTree(Y, N).


test1 :: Term
test1 = Compound "cons" [Compound "a" [], Compound "nil" []]


-- We could start with something simple, non-generic like this.




-- run  :: ∀a. Goal a -> Array a
-- step :: ∀a. Goal a -> Maybe {answer :: a, next :: (Goal a)}

-- reify :: Term -> Goal Term




main :: Effect Unit
main = do
  log "🍝"
