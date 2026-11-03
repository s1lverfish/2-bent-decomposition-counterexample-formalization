module

public import BentDecomposition.Basic
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace BentDecompositions.Family

/-- Lucas's low binary digit removes an even lower index. -/
theorem choose_even_mod_two (a j : ℕ) :
    (Nat.choose a (2*j) : ZMod 2) = (Nat.choose (a/2) j : ZMod 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := a) (k := 2*j)
  have hc := (ZMod.natCast_eq_natCast_iff (Nat.choose a (2*j))
    (Nat.choose (a%2) ((2*j)%2) * Nat.choose (a/2) ((2*j)/2)) 2).mpr h
  simpa using hc

/-- A single binary digit controls a power-of-two binomial coefficient. -/
theorem choose_pow_two_mod_two (a d : ℕ) :
    (Nat.choose a (2^d) : ZMod 2) = ((a / 2^d : ℕ) : ZMod 2) := by
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, Nat.mul_comm (2^d) 2, choose_even_mod_two, ih]
      simp only [Nat.div_div_eq_div_mul]


/-- Pascal cancellation of an initial binomial sum in characteristic two. -/
theorem partial_choose_mod_two (a b : ℕ) :
    (P (a+1) b : ZMod 2) = (Nat.choose a b : ZMod 2) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := a) (m := b)
  have hc := congrArg (fun z : ℤ => (z : ZMod 2)) h
  simpa [P, Int.cast_sum, Int.cast_mul, Int.cast_pow] using hc


/-- Pair the even indices of an initial finite sum. -/
theorem sum_even_indices (f : ℕ → ZMod 2) (b : ℕ) :
    (∑ j ∈ Finset.range (2*b+1), if Even j then f j else 0) =
      ∑ j ∈ Finset.range (b+1), f (2*j) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have he : 2*(b+1)+1 = (2*b+1)+1+1 := by omega
      conv_rhs => rw [Finset.sum_range_succ]
      rw [he, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hodd : ¬ Even (2*b+1) := by simp
      have heven : Even (2*b+1+1) := by simp [Nat.even_add]
      simp only [hodd, heven, ↓reduceIte, add_zero]
      rw [show 2*b+1+1 = 2*(b+1) by omega]


lemma P_zero (b : ℕ) : P 0 b = 1 := by
  have h : P 0 b = Nat.choose 0 0 := by
    unfold P
    apply Finset.sum_eq_single 0
    · intro j hj hne
      exact Nat.choose_eq_zero_of_lt (by omega)
    · intro h
      exact False.elim (h (by simp))
  simpa using h

/-- The scalar support calculation for an even-truncated dyadic binomial row. -/
theorem scalar_support_parity (d w : ℕ) (hw : w ≤ 4*2^d) :
    (∑ j ∈ Finset.range (2^d+1), (Nat.choose w (2*j) : ZMod 2)) =
      if w ≤ 1 ∨ 2*2^d+2 ≤ w then 1 else 0 := by
  simp_rw [choose_even_mod_two]
  have hp : (∑ j ∈ Finset.range (2^d+1), (Nat.choose (w/2) j : ZMod 2)) =
      (P (w/2) (2^d) : ZMod 2) := by simp [P]
  rw [hp]
  by_cases hsmall : w ≤ 1
  · have ha : w/2 = 0 := by omega
    simp [ha, P_zero, hsmall]
  · have hs : w/2 = (w/2-1)+1 := by omega
    rw [hs, partial_choose_mod_two, choose_pow_two_mod_two]
    have hbound : w/2-1 < 2*2^d := by omega
    by_cases hhigh : 2*2^d+2 ≤ w
    · have hlow : 2^d ≤ w/2-1 := by omega
      have hdiv : (w/2-1)/2^d = 1 :=
        Nat.div_eq_of_lt_le (by simpa using hlow) (by simpa using hbound)
      simp [hdiv, hhigh]
    · have hlow : w/2-1 < 2^d := by omega
      have hdiv : (w/2-1)/2^d = 0 := Nat.div_eq_of_lt hlow
      simp [hdiv, hsmall, hhigh]

/-- Equivalent filtered-index form used by the ANF evaluation. -/
theorem scalar_support_parity_even (d w : ℕ) (hw : w ≤ 4*2^d) :
    (∑ j ∈ Finset.range (2*2^d+1),
      if Even j then (Nat.choose w j : ZMod 2) else 0) =
      if w ≤ 1 ∨ 2*2^d+2 ≤ w then 1 else 0 := by
  rw [sum_even_indices]
  exact scalar_support_parity d w hw

end BentDecompositions.Family
