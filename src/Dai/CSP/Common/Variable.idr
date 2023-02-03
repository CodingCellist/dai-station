module Dai.CSP.Common.Variable

import Data.List
import Data.Maybe

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
  |||
  ||| N.B. You may want `getDom` instead.
  dom : List Nat

||| /!\ IF the variable is UNASSIGNED, returns the domain of the variable;
||| /!\ IF the variable is ASSIGNED, returns a SINGLETON LIST with the assigned
||| /!\   value!
public export
getDom : Variable -> List Nat
getDom (MkVar _ Nothing dom) = dom
getDom (MkVar _ (Just val) _) = [val]

||| Assign the given variable the given value.
public export
assign : (var : Variable) -> (val : Nat) -> Variable
assign var val = { assigned := Just val } var

||| Unassign the given variable (i.e. set its `assigned` status to `Nothing`).
public export
unassign : (var : Variable) -> Variable
unassign var = { assigned := Nothing } var

||| Select the first variable which isn't assigned. Crashes if an empty list
||| was passed or is reached.
public export
selectVar : List Variable -> Variable
selectVar [] = assert_total $ idris_crash "selectVar given/reached empty list"
selectVar (v :: vs) =
  if isNothing v.assigned
     then v
     else selectVar vs

||| Retrieve a value from the given variable's domain.
||| (currently just returns the first value; no cleverness here)
public export
selectVal : (var : Variable) -> Nat
selectVal var = case var.dom of
                     [] => assert_total $ idris_crash "pickVal_dom_empty_ERROR"
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
  show (MkVar idx Nothing dom) = "v\{show idx}: Ø \{show dom}"
  show (MkVar idx (Just x) dom) = "v\{show idx}: \{show x}"

