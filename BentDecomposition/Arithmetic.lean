module

public import BentDecomposition.Basic
public import Mathlib.Data.Nat.Choose.Factorization

@[expose] public section

namespace BentDecompositions.Family

private theorem pow_sub_one (k : ℕ) (hk : 2 ≤ k) :
    2^(k-1) = 2 * 2^(k-2) := by
  have he : k-1 = (k-2)+1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

/-- In the lower half of a dyadic binomial row, only the quarter-position
can be nonzero modulo eight (apart from the constant coefficient). -/
theorem choose_dyadic_dvd_eight (k j : ℕ) (hk : 3 ≤ k)
    (hj : 0 < j) (hjhalf : j < 2^(k-1)) (hjquarter : j ≠ 2^(k-2)) :
    8 ∣ Nat.choose (2^k) j := by
  have hpowpos : 0 < 2^(k-2) := by positivity
  have hjn : j ≤ 2^k := by
    have hexp : k = (k-1)+1 := by omega
    rw [hexp, pow_succ]
    omega
  have hval := Nat.factorization_choose_prime_pow_add_factorization Nat.prime_two hjn (by omega : j ≠ 0)
  have hcpos : Nat.choose (2^k) j ≠ 0 := (Nat.choose_pos hjn).ne'
  change 2^3 ∣ _
  apply (Nat.prime_two.pow_dvd_iff_le_factorization hcpos).mpr
  by_contra hn
  have hv : k-2 ≤ j.factorization 2 := by omega
  have hd := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : j ≠ 0)).mpr hv
  obtain ⟨a, ha⟩ := hd
  have hhalf := pow_sub_one k (by omega)
  rw [hhalf] at hjhalf
  have haone : a = 1 := by nlinarith
  rw [haone, mul_one] at ha
  exact hjquarter ha

theorem choose_dyadic_quarter_mod_eight (k : ℕ) (hk : 3 ≤ k) :
    Nat.choose (2^k) (2^(k-2)) % 8 = 4 := by
  have hp : 0 < 2^(k-2) := by positivity
  have hjn : 2^(k-2) ≤ 2^k := Nat.pow_le_pow_right (by omega) (by omega)
  have hval := Nat.factorization_choose_prime_pow_add_factorization Nat.prime_two hjn hp.ne'
  rw [Nat.factorization_pow_self Nat.prime_two] at hval
  have hcpos : Nat.choose (2^k) (2^(k-2)) ≠ 0 := (Nat.choose_pos hjn).ne'
  have hv : (Nat.choose (2^k) (2^(k-2))).factorization 2 = 2 := by omega
  have h4 : 4 ∣ Nat.choose (2^k) (2^(k-2)) := by
    change 2^2 ∣ _
    apply (Nat.prime_two.pow_dvd_iff_le_factorization hcpos).mpr
    omega
  have h8 : ¬ 8 ∣ Nat.choose (2^k) (2^(k-2)) := by
    intro h
    change 2^3 ∣ _ at h
    have hv3 := (Nat.prime_two.pow_dvd_iff_le_factorization hcpos).mp h
    omega
  rw [Nat.dvd_iff_mod_eq_zero] at h4 h8
  omega

theorem cast_choose_dyadic_low (k j : ℕ) (hk : 3 ≤ k)
    (hjhalf : j < 2^(k-1)) :
    (Nat.choose (2^k) j : ZMod 8) =
      (if j = 0 then 1 else 0) + (if j = 2^(k-2) then 4 else 0) := by
  have hp : 0 < 2^(k-2) := by positivity
  by_cases hz : j = 0
  · subst j
    simp [Ne.symm hp.ne']
  · by_cases hq : j = 2^(k-2)
    · subst j
      simp only [hp.ne', ↓reduceIte, zero_add]
      exact (ZMod.natCast_eq_natCast_iff' _ 4 8).mpr (by
        simpa using choose_dyadic_quarter_mod_eight k hk)
    · simp only [hz, hq, ↓reduceIte, zero_add]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr
        (choose_dyadic_dvd_eight k j hk (by omega) hjhalf hq)

theorem cast_P_dyadic_low (k b : ℕ) (hk : 3 ≤ k) (hb : b < 2^(k-1)) :
    (P (2^k) b : ZMod 8) = 1 + (if 2^(k-2) ≤ b then 4 else 0) := by
  simp only [P, Nat.cast_sum]
  calc
    _ = ∑ j ∈ Finset.range (b+1),
        ((if j = 0 then 1 else 0) + (if j = 2^(k-2) then 4 else 0) : ZMod 8) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact cast_choose_dyadic_low k j hk (by
        have := Finset.mem_range.mp hj
        omega)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']

theorem dyadic_div_two (k : ℕ) (hk : 1 ≤ k) :
    2^k / 2 = 2^(k-1) := by
  have he : k = (k-1)+1 := by omega
  conv_lhs => rw [he, pow_succ]
  omega

theorem dyadic_div_four (k : ℕ) (hk : 2 ≤ k) :
    2^k / 4 = 2^(k-2) := by
  have he : k = (k-2)+2 := by omega
  conv_lhs => rw [he, pow_add]
  norm_num

theorem P_dyadic_half_mod_eight (k : ℕ) (hk : 3 ≤ k) :
    P (2^k) (2^k/2-2) % 8 = 5 := by
  rw [dyadic_div_two k (by omega)]
  have hp : 2 ≤ 2^(k-2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k-2)
  have hh := pow_sub_one k (by omega)
  have hs := cast_P_dyadic_low k (2^(k-1)-2) hk (by omega)
  have hinc : 2^(k-2) ≤ 2^(k-1)-2 := by omega
  rw [ite_eq_left hinc] at hs
  norm_num at hs
  exact (ZMod.natCast_eq_natCast_iff' _ 5 8).mp hs

theorem P_dyadic_quarter_mod_eight (k : ℕ) (hk : 3 ≤ k) :
    P (2^k) (2^k/4-2) % 8 = 1 := by
  rw [dyadic_div_four k (by omega)]
  have hp : 2 ≤ 2^(k-2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k-2)
  have hh := pow_sub_one k (by omega)
  have hs := cast_P_dyadic_low k (2^(k-2)-2) hk (by omega)
  have hinc : ¬ 2^(k-2) ≤ 2^(k-2)-2 := by omega
  rw [ite_eq_right hinc, add_zero] at hs
  exact (ZMod.natCast_eq_natCast_iff' _ 1 8).mp hs

theorem dyadic_weight_discrepancy_mod_eight (k : ℕ) (hk : 3 ≤ k) :
    ((P (2^k) (2^k/2-2) : ℤ) + (2^k : ℕ) + 1 -
      2 * (P (2^k) (2^k/4-2) : ℤ)) % 8 = 4 := by
  have h1 := P_dyadic_half_mod_eight k hk
  have h2 := P_dyadic_quarter_mod_eight k hk
  have hn8 : 8 ∣ 2^k := by
    change 2^3 ∣ 2^k
    exact pow_dvd_pow 2 hk
  have hn := Nat.dvd_iff_mod_eq_zero.mp hn8
  have h1z : (P (2^k) (2^k/2-2) : ℤ) % 8 = 5 := by exact_mod_cast h1
  have h2z : (P (2^k) (2^k/4-2) : ℤ) % 8 = 1 := by exact_mod_cast h2
  have hnz : ((2^k : ℕ) : ℤ) % 8 = 0 := by exact_mod_cast hn
  omega

end BentDecompositions.Family
