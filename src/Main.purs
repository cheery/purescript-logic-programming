-- Implement a logic programming environment as a DSL within purescript.
module Main where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer, fix)
import Data.Array (zipWith, (!!), (:))
import Data.Foldable (any, foldr, intercalate)
import Data.List.Lazy (singleton)
import Data.List.Lazy.Types (List(..), nil)
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

type Goal = State -> List State

yes :: Goal -- prolog 'true'. -- 1, Equivalent to 'pure' in this context.
yes = \st -> singleton st

no :: Goal -- prolog 'false'. -- 0
no = \st -> nil

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
-- combineResults :: State -> State -> List State -- kind of like union, but needs to unify terms too.

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

reify :: Term -> State -> Term
reify (Var i) st = case lookup i st.variableBindings of
    Just v -> reify v st
    Nothing -> (Var i)
reify (Compound n xs) st = Compound n (map (\t -> reify t st) xs)

infix 6 eq as ≡
eq :: Term -> Term -> Goal
eq x y = \st -> unify (reifyVar x st) (reifyVar y st) st

-- Transforms the input state into state, where two input terms are the same.
-- To the unify, the bound input variables must be removed.

-- To unify two variables mean that they're the same value afterwards.
unify :: Term -> Term -> State -> List State
unify (Var i)        (Var j)        st = -- these are free variables, so neither appears in the 'st'
    pure $ st {
                variableBindings = insert i (Var j) st.variableBindings }
unify (Var i)        compound       st = 
    if false -- occurs i compound st
    then nil
    else pure $ st {
            variableBindings = insert i compound st.variableBindings }
unify compound       (Var j)        st =
    if false -- occurs j compound st
    then nil
    else pure $ st { 
                variableBindings = insert j compound st.variableBindings }
unify (Compound n xs) (Compound m ys) st | (n == m)
    = let
    zxy = zipWith (\x y st' -> unify (reifyVar x st') (reifyVar y st') st') xs ys
    in foldr (>=>) pure zxy st
unify (Compound n xs) (Compound m ys) st            = nil

-- Term must have passed the reifyVar first.
occurs :: Int -> Term -> State -> Boolean
occurs i (Var j) st = (i == j)
occurs i (Compound _ xs) st = any (\a -> occurs i (reifyVar a st) st) xs

blank :: State
blank = {variableBindings : empty, nextVariable : 0}


cons :: Term -> Term -> Term
cons x y = Compound "cons" [x, y]

emp :: Term
emp = Compound "emp" []

--list([]).
--list([X|R]) :- list(R).
-- listRule :: (Term -> Goal) -> Term -> Goal
-- listRule rec xs =
--     (xs ≡ emp)
--      ∨ (fresh $ \x -> fresh $ \r -> (xs ≡ cons x r ∧ rec r))
-- listR :: Term -> Goal
-- listR = fix listRule

listR :: Term -> Goal
listR xs
    = (xs ≡ emp)
    ∨ (fresh $ \x -> fresh $ \r -> (xs ≡ cons x r ∧ listR r))

example1 :: List State -- ?- list(R).
example1 = (fresh $ \x -> listR x) blank
-- [], [Y], ...



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
test1 = Compound "cons" [Compound "a" [], Compound "emp" []]



-- We are using De-bruijn indexing in LambdaTerm
data LambdaTerm = LVar Int                 -- x
                | Ap LambdaTerm LambdaTerm -- f x
                | Abs LambdaTerm           -- λ. body
                | NumLiteral Int           -- some number
type Type = Term

arrow :: Type -> Type -> Type
arrow x y = Compound "arrow" [x, y]

-- next time: instantiate / generalize

infer :: LambdaTerm -> Array Type -> Type -> Goal
infer (LVar n) env ty
    = case env !! n of
      Nothing -> no
      Just ty' -> (ty ≡ ty')
infer (Ap f x) env ty
    -- ∃ty_a. infer f env (ty_a → ty) ∧ infer x env ty_a
    = fresh $ \ty_a -> infer f env (arrow ty_a ty)
                     ∧ infer x env ty_a
infer (Abs f)  env ty
    -- ∃ty_a ty_b. ty ≡ arrow ty_a ty_b ∧ ...
    = fresh $ \ty_a -> fresh $ \ty_b ->
          (ty ≡ arrow ty_a ty_b)
        ∧ infer f (ty_a : env) ty_b
infer (NumLiteral n) env ty = (ty ≡ Compound "Number" [])

-- env ⊢ f : a →  b

identity_function :: LambdaTerm
identity_function = Abs (LVar 0)

-- The 'ty' will be the (Var 0), if this is called with blank state.
infer_identity_function :: State -> List State
infer_identity_function = fresh $ \ty -> infer identity_function [] ty


infer_function :: LambdaTerm → List Term
infer_function f = (fresh $ \ty -> infer f [] ty) blank
               >>= (reify (Var 0) >>> pure)

-- We could start with something simple, non-generic like this.

-- run  :: ∀a. Goal a -> List a
-- step :: ∀a. Goal a -> Maybe {answer :: a, next :: (Goal a)}

-- reify :: Term -> Goal Term




main :: Effect Unit
main = do
  log "🍝"
