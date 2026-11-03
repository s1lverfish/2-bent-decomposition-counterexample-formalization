module

public import BentDecomposition.Walsh

@[expose] public section

namespace BentDecompositions.Family
open scoped symmDiff

/-- Orthogonality of the binary characters. -/
theorem sum_character {n : ℕ} (z : Point n) :
    (∑ u : Point n, character u z) = if z = ∅ then (2 : ℤ)^n else 0 := by
  have hu : (Finset.univ : Finset (Point n)) = (Finset.univ : Point n).powerset := by
    ext u
    simp
  simp_rw [character_prod]
  rw [hu, ← Finset.prod_one_add]
  by_cases hz : z = ∅
  · subst z
    simp
  · rw [ite_eq_right hz]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Walsh–Parseval over the entire Boolean cube, using integer coefficients. -/
theorem walsh_parseval {n : ℕ} (f : BF n) :
    (∑ u : Point n, (walsh f u)^2) = (2 : ℤ)^(2*n) := by
  have he (u : Point n) : (walsh f u)^2 =
      ∑ x : Point n, ∑ y : Point n,
        sign (f x) * sign (f y) * character u (x ∆ y) := by
    simp only [walsh, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [character_comm u (x ∆ y), character_symmDiff,
      character_comm x u, character_comm y u]
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Point n, ∑ y : Point n,
        sign (f x) * sign (f y) * (∑ u : Point n, character u (x ∆ y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ x : Point n, (2 : ℤ)^n := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [sum_character]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y hy hne
        have hd : x ∆ y ≠ ∅ := by
          intro hh
          have : x = y := Finset.symmDiff_eq_empty.mp hh
          exact hne this.symm
        simp [hd]
      · simp
    _ = (2 : ℤ)^(2*n) := by
      simp [← pow_add, two_mul]

/-- A Boolean function with flat Walsh magnitude can exist only in even dimension. -/
theorem Bent.even_dimension {n : ℕ} {f : BF n} (hf : Bent f) : Even n := by
  have hflat (u : Point n) : (walsh f u)^2 = ((2 : ℤ)^(n/2))^2 := by
    rcases hf u with h | h <;> rw [h]; ring
  have hp := walsh_parseval f
  simp_rw [hflat] at hp
  have hs : (2 : ℤ)^n * ((2 : ℤ)^(n/2))^2 = (2 : ℤ)^(2*n) := by
    simpa using hp
  have he : (2 : ℤ)^(n+(n/2)*2) = (2 : ℤ)^(2*n) := by
    rw [pow_add, pow_mul]
    exact hs
  have hn : n+(n/2)*2 = 2*n :=
    (pow_right_injective₀ (by norm_num : (0 : ℤ) < 2)
      (by norm_num : (2 : ℤ) ≠ 1)) he
  exact ⟨n/2, by omega⟩

end BentDecompositions.Family
