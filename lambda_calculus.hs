{-# LANGUAGE UnicodeSyntax #-}

import Data.Set (Set, delete, difference, elemAt, empty, fromList, member, singleton, union)

alphaBet :: Set String
alphaBet = fromList $ map (: []) ['a' .. 'z']

type Var = String

data Type
  = RawType String
  | DType Type Term --  φM
  | UniType Var Type Type -- ∀x: φ.φ

data Term = VarTerm Var | Lambda Var Type Term | Applied Term Term

type Context = [(Var, Type)]

fv :: Term -> Set Var
fv (VarTerm v) = singleton v
fv (Lambda v s m) = delete v (fv m)
fv (Applied m n) = fv m `union` fv n

typeFv :: Type -> Set Var
typeFv (RawType s) = empty
typeFv (DType _ t) = fv t
typeFv (UniType v _ t) = delete v (typeFv t)

instance Show Term where
  show (VarTerm v) = v
  show (Lambda v s m) = "λ" ++ v ++ ":" ++ show s ++ "." ++ show m
  show (Applied m n) = "(" ++ show m ++ ")(" ++ show n ++ ")"

instance Show Type where
  show (RawType s) = s
  show (DType s m) = show s ++ show m
  show (UniType v s t) = "∀" ++ v ++ ":" ++ show s ++ "." ++ show t

sub :: Term -> Var -> Term -> Term
sub term@(VarTerm v) x n = if v == x then n else term
sub (Applied p q) x n = Applied (sub p x n) (sub q x n)
sub term@(Lambda y s p) x n
  | x == y = term
  | y `member` fv n =
    let z = elemAt 0 (difference alphaBet (fv n))
     in Lambda z s (sub (sub p y (VarTerm z)) x n)
  | otherwise = Lambda y s (sub p x n)

typeSub :: Type -> Var -> Term -> Type
typeSub t@(RawType s) _ _ = t
typeSub (DType s m) x n = DType (typeSub s x n) (sub m x n)
typeSub t@(UniType y phi m) x n
  | x == y = t
  | y `member` fv n =
    let z = elemAt 0 (difference alphaBet (fv n))
     in UniType
          z
          (typeSub (typeSub phi y (VarTerm z)) x n)
          (typeSub (typeSub m y (VarTerm z)) x n)
  | otherwise = UniType y (typeSub phi x n) (typeSub m x n)
