module Dai.Variable

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

||| Assign the given value to the given variable.
public export
assign : (val : Nat) -> (var : Variable) -> Variable
assign val var = { assigned := Just val } var

||| Retrieve a value from the given variable's domain.
||| (currently just returns the first value; no cleverness here)
public export
pickVal : (var : Variable) -> Nat
pickVal var = case var.dom of
                   [] => ?pickValDomEmptyERROR
                   (val :: vals) => val

