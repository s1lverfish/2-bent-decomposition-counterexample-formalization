module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace BentDecompositions

def sign (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by norm_num [sign]
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign]

@[simp] theorem sign_mul_self (z : ZMod 2) : sign z * sign z = 1 := by
  revert z; decide

@[simp] theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  revert a b; decide

@[simp] theorem sign_sub (a b : ZMod 2) : sign (a - b) = sign a * sign b := by
  revert a b; decide

end BentDecompositions
