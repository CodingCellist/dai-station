module Dai.CSP.Common.Variable

import Data.List

%default total

||| A variable in a binary CSP, containing:
|||   * its index
|||   * potential assigned value
|||   * its domain (allowed values)
public export
record Variable where
  constructor MkVar

  ||| Variables don't have a name, only an index.
  idx : Nat

  ||| The currently assigned value (if any).
  assigned : Maybe Nat

  ||| The domain (list of permitted assignemnts).
  dom : List Nat

||| Assign the given variable the given value.
public export
assign : (var : Variable) -> (val : Nat) -> Variable
assign var val = { assigned := Just val } var

||| Retrieve a value from the given variable's domain.
||| (currently just returns the first value; no cleverness here)
public export
pickVal : (var : Variable) -> Nat
pickVal var = case var.dom of
                   [] => ?pickValDomEmptyERROR
                   (val :: vals) => val

||| Remove the given value from the variable's domain.
public export
delVal : (var : Variable) -> (val : Nat) -> Variable
delVal var val = { dom $= delete val } var

------------------------------------------------------------------------
-- Interfaces

public export
Eq Variable where
  (==) (MkVar idxA _ _) (MkVar idxB _ _) = idxA == idxB

public export
Show Variable where
  show (MkVar idx Nothing dom) = "v\{show idx}:\t Ø \{show dom}"
  show (MkVar idx (Just x) dom) = "v\{show idx}:\t \{show x}"

