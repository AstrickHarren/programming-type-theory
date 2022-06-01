{-# LANGUAGE UnicodeSyntax #-}

import Control.Applicative (Applicative (liftA2))
import Data.Maybe (fromJust)
import Data.Set (Set, delete, difference, elemAt, empty, fromList, member, singleton, union)
import Distribution.Simple.Setup (emptySDistFlags)

alphaBet :: Set String
alphaBet = fromList $ map (: []) ['a' .. 'z']

type Var = String

data Type
  = RawType String
  | DType Type Term --  φM
  | UniType Var Type Type -- ∀x: φ.φ
  deriving (Eq)

data Term = VarTerm Var | Lambda Var Type Term | Applied Term Term deriving (Eq)

type Context = [(Var, Type)]

fv :: Term -> Set Var
fv (VarTerm v) = singleton v
fv (Lambda v s m) = delete v (fv m)
fv (Applied m n) = fv m `union` fv n

typeFv :: Type -> Set Var
typeFv (RawType s) = empty
typeFv (DType s t) = typeFv s `union` fv t
typeFv (UniType v s t) = delete v (typeFv s `union` typeFv t)

instance Show Term where
  show (VarTerm v) = v
  show (Lambda v s m) = "λ" ++ v ++ ":" ++ show s ++ "." ++ show m
  show (Applied m n) = "(" ++ show m ++ ")(" ++ show n ++ ")"

instance Show Type where
  show (RawType s) = s
  show (DType s m) = show s ++ show m
  show (UniType v s t) =
    if v `member` typeFv t
      then "∀" ++ v ++ ":" ++ show s ++ "." ++ show t
      else show s ++ " -> " ++ show t

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

typeOf :: Context -> Term -> Type
typeOf ctx (VarTerm v) = fromJust $ lookup v ctx
typeOf ctx (Applied m n) = case typeOf ctx m of
  UniType x s t -> if typeOf ctx n == s then typeSub t x n else error "type check error: wrong application"
  _ -> error "type check error"
typeOf ctx (Lambda x s m) = UniType x s (typeOf ((x, s) : ctx) m)

----- Utilities

binaryType :: Type -> Term -> Term -> Type
binaryType s a = DType (DType s a)

imply :: Type -> Type -> Type
imply a b =
  let z = elemAt 0 $ alphaBet `difference` (typeFv a `union` typeFv b)
   in UniType z a b

------ Test
tSet = RawType "S"

belongsTo = binaryType $ RawType "∈"

isSubsetOf = binaryType $ RawType "⊂"

subsetMeaning =
  UniType
    "x"
    tSet
    ( (VarTerm "x" `belongsTo` VarTerm "A")
        `imply` (VarTerm "x" `belongsTo` VarTerm "B")
    )

defSubset =
  UniType
    "A"
    tSet
    ( UniType "B" tSet $
        (VarTerm "A" `isSubsetOf` VarTerm "B")
          `imply` subsetMeaning
    )

interpretSubset =
  UniType
    "A"
    tSet
    ( UniType "B" tSet $
        subsetMeaning `imply` (VarTerm "A" `isSubsetOf` VarTerm "B")
    )

emptySet = VarTerm "∅"

emptySetIsSet = ("∅", tSet)

emptySetIsBottom = UniType "A" tSet (emptySet `isSubsetOf` VarTerm "A")

axioms =
  [ emptySetIsSet,
    ("empty set is bottom", emptySetIsBottom),
    ("interpret of subset", defSubset)
  ]

verify :: Context -> [(Type, Term)] -> Bool
verify ctx = all (liftA2 (==) fst (typeOf ctx . snd))

props = [(emptySetSubsetSelf, emptySetSubsetSelfProof), (emptySetSubsetAllMeaning, emptySetSubsetAllMeaningProof)]

emptySetSubsetSelf = emptySet `isSubsetOf` emptySet

emptySetSubsetSelfProof = Applied (VarTerm "empty set is bottom") emptySet

emptySetSubsetAllMeaning =
  UniType
    "A"
    tSet
    ( UniType "x" tSet $
        (VarTerm "x" `belongsTo` VarTerm "∅")
          `imply` (VarTerm "x" `belongsTo` VarTerm "A")
    )

emptySetSubsetAllMeaningProof =
  Lambda "A" tSet $
    Applied
      (Applied (Applied (VarTerm "interpret of subset") (VarTerm "∅")) (VarTerm "A"))
      (Applied (VarTerm "empty set is bottom") (VarTerm "A"))