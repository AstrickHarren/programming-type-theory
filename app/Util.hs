module Util where

import Grammar

binaryType :: String -> Term -> Term -> Type
binaryType p x = SuchThat (SuchThat (Type p) x)
