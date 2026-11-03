module

public import BentDecomposition.Basic

@[expose] public section

namespace BentDecompositions.Family

/-- The squarefree monomials are linearly independent as Boolean functions. -/
theorem evalANF_zero_injective {n : ℕ} (a : Point n → ZMod 2)
    (h : ∀ x, evalANF a x = 0) : ∀ T, a T = 0 := by
  intro T
  refine Finset.strongInductionOn T ?_
  intro T ih
  have hs : evalANF a T = a T := by
    unfold evalANF
    calc
      _ = a T * monomial T T := by
        apply Finset.sum_eq_single T
        · intro U hU hne
          by_cases hsub : U ⊆ T
          · rw [ih U (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)]
            simp
          · simp [monomial, hsub]
        · simp
      _ = a T := by simp [monomial]
  rw [← hs]
  exact h T

theorem evalANF_injective {n : ℕ} :
    Function.Injective (evalANF (n := n)) := by
  intro a b hab
  have hzero : ∀ x, evalANF (fun T => a T - b T) x = 0 := by
    intro x
    simp only [evalANF, sub_mul, Finset.sum_sub_distrib]
    have hx := congrFun hab x
    exact sub_eq_zero.mpr hx
  have h := evalANF_zero_injective _ hzero
  funext T
  exact sub_eq_zero.mp (h T)

/-- An even nonzero highest layer cannot be represented by lower-degree terms. -/
theorem Fn_not_degree_le {n : ℕ} (hn : 0 < n/2) (he : Even (n/2)) :
    ¬ DegreeLE (Fn n) (n/2-1) := by
  rintro ⟨a, ha, heq⟩
  have hcoef : familyCoefficients n = a :=
    evalANF_injective (by simpa only [Fn] using heq)
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Point n)) (by simp; omega : n/2 ≤ (Finset.univ : Point n).card)
  have htop : familyCoefficients n T = 1 := by simp [familyCoefficients, hc, he]
  have hz := ha T (by omega)
  rw [← hcoef, htop] at hz
  exact one_ne_zero hz

@[simp] theorem evalANF_empty {n : ℕ} (a : Point n → ZMod 2) :
    evalANF a ∅ = a ∅ := by
  simp [evalANF, monomial]

@[simp] theorem Fn_empty_one (n : ℕ) : Fn n ∅ = 1 := by
  simp [Fn, familyCoefficients]

/-- The all-dyadic exact-degree statement, expressed without an assumed
uniqueness theorem: degree at most the half-dimension, but not one less. -/
theorem Fn_exact_degree (k : ℕ) (hk : 3 ≤ k) :
    DegreeLE (Fn (2^k)) ((2^k)/2) ∧
      ¬ DegreeLE (Fn (2^k)) ((2^k)/2-1) := by
  refine ⟨Fn_degree_le _, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hm : (2^(3+j))/2 = 2^(j+2) := by
    rw [show 3+j = (j+2)+1 by omega, pow_succ]
    omega
  apply Fn_not_degree_le
  · rw [hm]
    exact pow_pos (by decide) _
  · rw [hm]
    rw [show j+2 = (j+1)+1 by omega, pow_succ]
    exact ⟨2^(j+1), by omega⟩

theorem Fn_ne_zero (n : ℕ) : Fn n ≠ 0 := by
  intro h
  have hx := congrFun h ∅
  simp at hx

end BentDecompositions.Family
