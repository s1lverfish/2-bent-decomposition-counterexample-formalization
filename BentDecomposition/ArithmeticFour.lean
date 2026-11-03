module

public import BentDecomposition.Arithmetic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace BentDecompositions.Family
open Polynomial

private theorem square_four (a : (ZMod 4)[X]) :
    (1+2*a+a^2)^2 = 1+2*a^2+a^4 := by
  have h4 : (4 : (ZMod 4)[X]) = 0 := by
    have h : (4 : ZMod 4) = 0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (Polynomial.C (R := ZMod 4)) h
  have h6 : (6 : (ZMod 4)[X]) = 2 := by
    have h : (6 : ZMod 4) = 2 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (Polynomial.C (R := ZMod 4)) h
  calc
    _ = 1+4*a+6*a^2+4*a^3+a^4 := by ring
    _ = _ := by rw [h4,h6]; ring

/-- Coefficientwise dyadic binomial congruence modulo four. -/
theorem dyadic_binomial_mod_four (q : ℕ) :
    ((1+X)^(2^(q+1)) : (ZMod 4)[X]) =
      1+2*X^(2^q)+X^(2^(q+1)) := by
  induction q with
  | zero => norm_num; ring
  | succ q ih =>
    have he : 2^(q+1+1) = 2^(q+1)*2 := by rw [pow_succ]
    have he1 : 2^(q+1) = 2^q*2 := by rw [pow_succ]
    calc
      _ = (((1+X)^(2^(q+1)))^2 : (ZMod 4)[X]) := by
        rw [← pow_mul]
        congr 1
      _ = (1+2*X^(2^q)+(X^(2^q))^2)^2 := by rw [ih, ← pow_mul, ← he1]
      _ = 1+2*(X^(2^q))^2+(X^(2^q))^4 := square_four _
      _ = 1+2*X^(2^(q+1))+X^(2^(q+1+1)) := by
        rw [← pow_mul, ← pow_mul, ← he1, he, he1]
        congr 2
        omega

theorem sum_shifted_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (s b : ℕ) :
    (∑ i ∈ Finset.range (b+1), if s ≤ i then f (i-s) else 0) =
      if s ≤ b then ∑ j ∈ Finset.range (b-s+1), f j else 0 := by
  by_cases hsb : s ≤ b
  · rw [ite_eq_left hsb]
    have he : b+1 = s+(b-s+1) := by omega
    rw [he, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range s, if s ≤ i then f (i-s) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [ite_eq_right (by have := Finset.mem_range.mp hi; omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  · rw [ite_eq_right hsb]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right (by have := Finset.mem_range.mp hi; omega)]

theorem choose_dyadic_add_low_mod_four (q a i : ℕ) (hi : i < 2^(q+1)) :
    (Nat.choose (2^(q+1)+a) i : ZMod 4) =
      (Nat.choose a i : ZMod 4) + 2*(if 2^q ≤ i then (Nat.choose a (i-2^q) : ZMod 4) else 0) := by
  have hp : ((1+X)^(2^(q+1)+a) : (ZMod 4)[X]) =
      (1+2*X^(2^q)+X^(2^(q+1)))*(1+X)^a := by
    rw [pow_add, dyadic_binomial_mod_four]
  have hc := congrArg (fun p : (ZMod 4)[X] => p.coeff i) hp
  simp only [add_mul, one_mul, coeff_add, mul_assoc, coeff_ofNat_mul, coeff_X_pow_mul',
    coeff_one_add_X_pow] at hc
  simpa [show ¬ 2^(q+1) ≤ i by omega] using hc

theorem cast_P_dyadic_add_mod_four (q a b : ℕ) (hb : b < 2^(q+1)) :
    (P (2^(q+1)+a) b : ZMod 4) =
      (P a b : ZMod 4) + 2 * (if 2^q ≤ b then (P a (b-2^q) : ZMod 4) else 0) := by
  simp only [P, Nat.cast_sum]
  calc
    _ = ∑ i ∈ Finset.range (b+1),
        ((Nat.choose a i : ZMod 4) +
          2*(if 2^q ≤ i then (Nat.choose a (i-2^q) : ZMod 4) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact choose_dyadic_add_low_mod_four q a i (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_shifted_range (fun j => (Nat.choose a j : ZMod 4)) (2^q) b]

/-- Complete binomial rows remain complete when padded with zero terms. -/
theorem P_eq_two_pow (a b : ℕ) (hab : a ≤ b) : P a b = 2^a := by
  rw [P, ← Nat.sum_range_choose a]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hja
  apply Nat.choose_eq_zero_of_lt
  have := Finset.mem_range.mp hj
  have hnot : ¬ j < a+1 := by simpa using hja
  omega

theorem P_pred_add_one (a : ℕ) (ha : 1 ≤ a) : P a (a-1) + 1 = 2^a := by
  have he : a-1+1=a := by omega
  rw [P, he]
  have hs := Nat.sum_range_choose a
  rw [Finset.sum_range_succ, Nat.choose_self] at hs
  exact hs

theorem P_sub_two_add (a : ℕ) (ha : 2 ≤ a) : P a (a-2) + a + 1 = 2^a := by
  have he : a-2+1=a-1 := by omega
  rw [P, he]
  have hs := Nat.sum_range_choose a
  rw [Finset.sum_range_succ] at hs
  have hs2 : a = (a-1)+1 := by omega
  conv_lhs at hs => rw [hs2, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.choose_succ_self_right] at hs
  simpa only [← hs2] using hs

private theorem cast_two_pow_zero_mod_four (a : ℕ) (ha : 2 ≤ a) :
    ((2^a : ℕ) : ZMod 4) = 0 := by
  apply (ZMod.natCast_eq_zero_iff _ 4).mpr
  change 2^2 ∣ 2^a
  exact pow_dvd_pow 2 ha

/-- The correction coming from the lower Hamming ball. -/
def lowCorrection (n t : ℕ) : ℕ := if t = 0 then n+1 else if t = 1 then 1 else 0

theorem cast_P_correction_mod_four (m t : ℕ) (hm : 4 ≤ m) (h4m : 4 ∣ m)
    (ht : t ≤ m-2) :
    (P (m-t) (m-2) + lowCorrection (2*m) t : ZMod 4) = 0 := by
  by_cases ht0 : t = 0
  · subst t
    simp only [Nat.sub_zero, lowCorrection, ite_true, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    have hrow := P_sub_two_add m (by omega)
    have hrowz : (P m (m-2) : ZMod 4) + (m : ZMod 4) + 1 = 0 := by
      have hz := congrArg (fun a : ℕ => (a : ZMod 4)) hrow
      simpa [cast_two_pow_zero_mod_four m (by omega)] using hz
    have hmz : (m : ZMod 4) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h4m
    rw [hmz] at hrowz ⊢
    simpa using hrowz
  · by_cases ht1 : t = 1
    · subst t
      simp only [lowCorrection, ite_eq_right (by decide : ¬ (1:ℕ)=0), ite_true, Nat.cast_one]
      have hrow := P_pred_add_one (m-1) (by omega)
      have he : m-1-1=m-2 := by omega
      rw [he] at hrow
      have hz := congrArg (fun a : ℕ => (a : ZMod 4)) hrow
      simpa [cast_two_pow_zero_mod_four (m-1) (by omega)] using hz
    · have htm : m-t ≤ m-2 := by omega
      have hmt : 2 ≤ m-t := by omega
      rw [P_eq_two_pow (m-t) (m-2) htm]
      simp [lowCorrection, ht0, ht1, cast_two_pow_zero_mod_four (m-t) hmt]

theorem selected_count_cast_mod_four (q t : ℕ) (hq : 1 ≤ q)
    (ht : t ≤ 2^(q+1)-2) :
    (P (2*2^(q+1)-t) (2^(q+1)-2) : ZMod 4) +
      (lowCorrection (2*2^(q+1)) t : ZMod 4) =
        2*(P (2*2^(q+1)-t) (2^q-2) : ZMod 4) := by
  have hs : 2 ≤ 2^q := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hq
  have hm : 2^(q+1) = 2*2^q := by rw [pow_succ, Nat.mul_comm]
  have h4m : 4 ∣ 2^(q+1) := by
    change 2^2 ∣ 2^(q+1)
    exact pow_dvd_pow 2 (by omega)
  have hsplit : 2*2^(q+1)-t = 2^(q+1)+(2^(q+1)-t) := by omega
  have hlarge := cast_P_dyadic_add_mod_four q (2^(q+1)-t) (2^(q+1)-2) (by omega)
  have hsmall := cast_P_dyadic_add_mod_four q (2^(q+1)-t) (2^q-2) (by omega)
  have hle : 2^q ≤ 2^(q+1)-2 := by omega
  have hnot : ¬ 2^q ≤ 2^q-2 := by omega
  have hsub : 2^(q+1)-2-2^q = 2^q-2 := by omega
  rw [ite_eq_left hle, hsub] at hlarge
  rw [ite_eq_right hnot, mul_zero, add_zero] at hsmall
  have hcorr := cast_P_correction_mod_four (2^(q+1)) t (by omega) h4m ht
  rw [hsplit, hlarge, hsmall]
  calc
    _ = ((P (2^(q+1)-t) (2^(q+1)-2) : ZMod 4) +
          (lowCorrection (2*2^(q+1)) t : ZMod 4)) +
        2*(P (2^(q+1)-t) (2^q-2) : ZMod 4) := by ring
    _ = _ := by rw [hcorr, zero_add]

theorem selected_count_mod_four (k t : ℕ) (hk : 3 ≤ k) (ht : t ≤ 2^k/2-2) :
    (P (2^k-t) (2^k/2-2) + lowCorrection (2^k) t) % 4 =
      (2*P (2^k-t) (2^k/4-2)) % 4 := by
  have hhalf := dyadic_div_two k (by omega)
  have hquarter := dyadic_div_four k (by omega)
  have he : k-2+1=k-1 := by omega
  have hn : 2^k = 2*2^(k-1) := by
    have h : k=(k-1)+1 := by omega
    conv_lhs => rw [h, pow_succ]
    omega
  have hc := selected_count_cast_mod_four (k-2) t (by omega) (by simpa [he, hhalf] using ht)
  rw [he, ← hn, ← hhalf, ← hquarter] at hc
  apply (ZMod.natCast_eq_natCast_iff' _ _ 4).mp
  simpa using hc

end BentDecompositions.Family
