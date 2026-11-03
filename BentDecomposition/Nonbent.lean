module

public import BentDecomposition.Support
public import BentDecomposition.Arithmetic
public import BentDecomposition.Walsh
public import BentDecomposition.Degree

@[expose] public section

namespace BentDecompositions.Family

/-- The support size is six modulo eight throughout the dyadic family. -/
theorem Fn_weight_mod_eight (k : ℕ) (hk : 3 ≤ k) :
    (support (2^k)).card % 8 = 6 := by
  have hn : 8 ≤ 2^k := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
  rw [support_card (2^k) hn]
  have hp := P_dyadic_half_mod_eight k hk
  have hdiv : 8 ∣ 2^k := by
    change 2^3 ∣ 2^k
    exact pow_dvd_pow 2 hk
  have hmod := Nat.dvd_iff_mod_eq_zero.mp hdiv
  omega

/-- Zero-frequency Walsh value in terms of the actual polynomial's support. -/
theorem Fn_walsh_zero (k : ℕ) (hk : 3 ≤ k) :
    walsh (Fn (2^k)) ∅ = (2 : ℤ)^(2^k) - 2 * ((support (2^k)).card : ℤ) := by
  have hf : (Finset.univ.filter (fun x : Point (2^k) => Fn (2^k) x = 1)) =
      support (2^k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fn_eq_indicator k hk x]
    by_cases hx : x ∈ support (2^k) <;> simp [hx]
  simp only [walsh, character_empty, mul_one]
  rw [sum_sign_eq_card_sub_twice, hf]
  simp

/-- No member of the infinite family is itself bent. -/
theorem Fn_not_bent (k : ℕ) (hk : 3 ≤ k) : ¬ Bent (Fn (2^k)) := by
  intro hb
  have hn : 8 ≤ 2^k := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
  have hm : 4 ≤ (2^k)/2 := by omega
  have hpow16 : (16 : ℤ) ∣ (2 : ℤ)^((2^k)/2) := by
    change (2 : ℤ)^4 ∣ (2 : ℤ)^((2^k)/2)
    exact pow_dvd_pow 2 hm
  have hwal : (16 : ℤ) ∣ walsh (Fn (2^k)) ∅ := by
    rcases hb ∅ with h | h
    · rw [h]; exact hpow16
    · rw [h]; exact dvd_neg.mpr hpow16
  have hcube : (16 : ℤ) ∣ (2 : ℤ)^(2^k) := by
    change (2 : ℤ)^4 ∣ (2 : ℤ)^(2^k)
    exact pow_dvd_pow 2 (by omega)
  have ht : (16 : ℤ) ∣ 2 * ((support (2^k)).card : ℤ) := by
    have h := dvd_sub hcube hwal
    rw [Fn_walsh_zero k hk] at h
    convert h using 1; ring
  have hmod := Fn_weight_mod_eight k hk
  have hmodz : ((support (2^k)).card : ℤ) % 8 = 6 := by exact_mod_cast hmod
  obtain ⟨a, ha⟩ := ht
  omega

end BentDecompositions.Family
