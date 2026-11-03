module

public import BentDecomposition.Support
public import BentDecomposition.ArithmeticFour
public import BentDecomposition.Restriction
public import BentDecomposition.Walsh
public import BentDecomposition.Degree
public import BentDecomposition.Nonbent

@[expose] public section

namespace BentDecompositions.Family

/-- No sum of two arbitrary bent functions represents any member of the
infinite dyadic family. There is no finite cutoff on k. -/
theorem Fn_not_sum_two_bent (k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ g h : BF (2^k), Bent g ∧ Bent h ∧
      ∀ x, Fn (2^k) x = g x + h x := by
  have hn : 8 ≤ (2 : ℕ)^k := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
  rintro ⟨g, h, hg, hh, hsum⟩
  have hs := Fn_eq_indicator k hk
  have hgh : ∀ x, g x+h x = if x ∈ support (2^k) then 1 else 0 := by
    intro x
    rw [← hsum x, hs x]
  have horth : ∀ T : Point (2^k), T.card ≤ 2^k/2-2 →
      (∑ x ∈ support (2^k), (delta x-g x)*monomial T x) = 0 := by
    intro T hT
    have hnat : ((support (2^k)).filter (fun x => T ⊆ x)).card % 4 =
        (2*P (2^k-T.card) (2^k/4-2)) % 4 := by
      rw [support_selected_card _ hn]
      simpa only [lowerCorrection, lowCorrection] using selected_count_mod_four k T.card hk hT
    have hcount : (((support (2^k)).filter (fun x => T ⊆ x)).card : ℤ) % 4 =
        (2*(P (2^k-T.card) (2^k/4-2) : ℤ)) % 4 := by exact_mod_cast hnat
    have hp := parity_from_divisibility g T (P (2^k-T.card) (2^k/4-2) : ℤ)
      hcount (support_moment_dvd_four g h hg hh hgh T (by omega) hT)
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, delta_selected_sum]
    simpa using sub_eq_zero.mpr hp.symm
  obtain ⟨c, b, hab⟩ := family_restriction_affine hn hs (fun x => delta x-g x) horth
  have hsum' : ∀ x, (g x+affine c b x)+(h x+affine c b x) =
      if x ∈ support (2^k) then 1 else 0 := by
    intro x
    rw [add_add_add_comm, ZModModule.add_self, add_zero]
    exact hgh x
  have hnorm : ∀ x ∈ support (2^k), g x+affine c b x = delta x := by
    intro x hx
    rw [← hab x hx]
    ring
  have hd := normalized_discrepancy_dvd _ _ (bent_add_affine hg c b)
    (bent_add_affine hh c b) hsum' hnorm
  rw [support_card _ hn, delta_card] at hd
  push_cast at hd
  exact discrepancy_contradiction (n := 2^k) _ (by omega) hd
    (dyadic_weight_discrepancy_mod_eight k hk)

/-- Zero, one, or two same-domain bent summands. -/
def SumAtMostTwo {n : ℕ} (f : BF n) : Prop :=
  f = 0 ∨ Bent f ∨ ∃ g h : BF n, Bent g ∧ Bent h ∧ ∀ x, f x = g x+h x

theorem Fn_not_at_most_two (k : ℕ) (hk : 3 ≤ k) :
    ¬ SumAtMostTwo (Fn (2^k)) := by
  rintro (hz | hb | htwo)
  · exact Fn_ne_zero _ hz
  · exact Fn_not_bent k hk hb
  · exact Fn_not_sum_two_bent k hk htwo

/-- The full infinite family: for every k≥3 the polynomial
1+σ₂+σ₄+⋯+σ_(2^(k−1)) has exact degree 2^(k−1) and cannot be a sum
of at most two arbitrary bent functions in the same 2^k variables. -/
theorem full_infinite_family (k : ℕ) (hk : 3 ≤ k) :
    DegreeLE (Fn (2^k)) (2^k/2) ∧
    ¬ DegreeLE (Fn (2^k)) (2^k/2-1) ∧
    ¬ SumAtMostTwo (Fn (2^k)) := by
  exact ⟨(Fn_exact_degree k hk).1, (Fn_exact_degree k hk).2,
    Fn_not_at_most_two k hk⟩

#print axioms Fn_not_sum_two_bent
#print axioms Fn_not_at_most_two
#print axioms full_infinite_family

end BentDecompositions.Family
