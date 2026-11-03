module

public import BentDecomposition.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace BentDecompositions.Family

lemma monomial_prod {n : ℕ} (T x : Point n) :
    monomial T x = ∏ i ∈ T, (if i ∈ x then (1 : ZMod 2) else 0) := by
  induction T using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, ← ih]
    by_cases hx : i ∈ x <;> by_cases hT : T ⊆ x <;>
      simp [monomial, Finset.insert_subset_iff, hx, hT]

lemma complement_polynomial {n : ℕ} (T x : Point n) :
    (∑ U ∈ T.powerset, monomial U x) =
      if Disjoint T x then (1 : ZMod 2) else 0 := by
  simp_rw [monomial_prod]
  rw [← Finset.prod_one_add]
  by_cases hd : Disjoint T x
  · rw [ite_eq_left hd]
    apply Finset.prod_eq_one
    intro i hi
    have hx : i ∉ x := fun hx => Finset.disjoint_left.mp hd hi hx
    simp [hx]
  · rw [ite_eq_right hd]
    obtain ⟨i, hi, hx⟩ := Finset.not_disjoint_iff.mp hd
    apply Finset.prod_eq_zero hi
    simp [hx]
    decide

lemma orthogonal_complement {n : ℕ} (S : Finset (Point n)) (a : BF n) (R : ℕ)
    (h : ∀ T : Point n, T.card ≤ R → (∑ x ∈ S, a x * monomial T x) = 0)
    (T : Point n) (hT : T.card ≤ R) :
    (∑ x ∈ S, if Disjoint T x then a x else 0) = 0 := by
  have he : (∑ x ∈ S, a x * ∑ U ∈ T.powerset, monomial U x) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro U hU
    exact h U (le_trans (Finset.card_le_card (Finset.mem_powerset.mp hU)) hT)
  simpa only [complement_polynomial, mul_ite, mul_one, mul_zero] using he

/-- Triangular uniqueness on the union of the lower radius-one ball and an
upper Hamming ball. No finite-dimensional rank computation is required. -/
theorem restriction_zero_of_low_zero {n R : ℕ} (S : Finset (Point n)) (a : BF n)
    (hS : ∀ x ∈ S, x.card ≤ 1 ∨ n - x.card ≤ R)
    (hlow : ∀ x : Point n, x.card ≤ 1 → a x = 0)
    (horth : ∀ T : Point n, T.card ≤ R → (∑ x ∈ S, a x * monomial T x) = 0) :
    ∀ y ∈ S, a y = 0 := by
  have hall : ∀ k : ℕ, ∀ y : Point n, y.card = k → y ∈ S → a y = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y hy hmem
      rcases hS y hmem with hsmall | hlarge
      · exact hlow y hsmall
      · have hcard : yᶜ.card ≤ R := by
          simpa only [Finset.card_compl, Fintype.card_fin] using hlarge
        have ho := orthogonal_complement S a R horth yᶜ hcard
        have hs : (∑ x ∈ S, if Disjoint yᶜ x then a x else 0) = a y := by
          calc
            _ = (if Disjoint yᶜ y then a y else 0) := by
              apply Finset.sum_eq_single y
              · intro x hx hxy
                by_cases hd : Disjoint yᶜ x
                · rw [ite_eq_left hd]
                  have hsub : x ⊆ y := by
                    have hh := Finset.subset_compl_iff_disjoint_left.mpr hd
                    simpa using hh
                  have hlt : x.card < y.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hxy⟩)
                  exact ih x.card (by omega) x rfl hx
                · simp [hd]
              · intro hnot
                exact False.elim (hnot hmem)
            _ = a y := by
              have hd : Disjoint yᶜ y := Finset.disjoint_left.mpr (by intro i hi hy; exact (Finset.mem_compl.mp hi) hy)
              simp [hd]
        rw [hs] at ho
        exact ho
  intro y hy
  exact hall y.card y rfl hy

open scoped symmDiff

lemma total_monomial_zero {n : ℕ} (T : Point n) (hT : T.card < n) :
    (∑ x : Point n, monomial T x) = 0 := by
  classical
  have hn : ¬ ∀ i : Fin n, i ∈ T := by
    intro hall
    have he := Finset.eq_univ_iff_forall.mpr hall
    have hc : T.card = n := by simp [he]
    omega
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hm (x : Point n) : monomial T (x ∆ {i}) = monomial T x := by
    have hs : T ⊆ x ∆ {i} ↔ T ⊆ x := by
      constructor <;> intro hh j hj
      · have hji : j ≠ i := fun he => hi (he ▸ hj)
        have hhj := hh hj
        simpa [Finset.mem_symmDiff, hji] using hhj
      · have hji : j ≠ i := fun he => hi (he ▸ hj)
        have hhj := hh hj
        simpa [Finset.mem_symmDiff, hji] using hhj
    simp only [monomial, hs]
  apply Finset.sum_ninvolution (fun x : Point n => x ∆ {i})
  · intro x
    rw [hm]
    exact ZModModule.add_self _
  · intro x hx he
    have hmem : i ∈ x ∆ {i} ↔ i ∈ x := by rw [he]
    by_cases hh : i ∈ x <;> simp [Finset.mem_symmDiff, hh] at hmem
  · intro x
    exact Finset.mem_univ _
  · intro x
    ext j
    by_cases hj : j = i <;> by_cases hx : j ∈ x <;>
      simp [hj, hx]

lemma monomial_mul {n : ℕ} (U T x : Point n) :
    monomial U x * monomial T x = monomial (U ∪ T) x := by
  by_cases hu : U ⊆ x <;> by_cases ht : T ⊆ x <;>
    simp [monomial, Finset.union_subset_iff, hu, ht]

lemma total_degreeLE_monomial {n d : ℕ} (p : BF n) (hp : DegreeLE p d)
    (T : Point n) (hT : d + T.card < n) :
    (∑ x : Point n, p x * monomial T x) = 0 := by
  obtain ⟨c, hc, rfl⟩ := hp
  simp only [evalANF, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro U hU
  by_cases hu : d < U.card
  · simp [hc U hu]
  · have hcard : (U ∪ T).card < n := by
      have hh := Finset.card_union_le U T
      omega
    calc
      (∑ x : Point n, c U * monomial U x * monomial T x) =
          c U * ∑ x : Point n, monomial (U ∪ T) x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [mul_assoc, monomial_mul]
      _ = 0 := by rw [total_monomial_zero _ hcard, mul_zero]

lemma affine_sum {n : ℕ} (c : ZMod 2) (b : Fin n → ZMod 2) (x : Point n) :
    affine c b x = c + ∑ i : Fin n, b i * monomial {i} x := by
  simp [affine, monomial, mul_ite]

lemma total_degreeLE_affine_monomial {n d : ℕ} (p : BF n) (hp : DegreeLE p d)
    (c : ZMod 2) (b : Fin n → ZMod 2) (T : Point n) (hT : d + T.card + 1 < n) :
    (∑ x : Point n, p x * affine c b x * monomial T x) = 0 := by
  have he (x : Point n) : p x * affine c b x * monomial T x =
      c * (p x * monomial T x) +
        ∑ i : Fin n, b i * (p x * monomial ({i} ∪ T) x) := by
    rw [affine_sum, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      rw [← monomial_mul]
      ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    total_degreeLE_monomial p hp T (by omega), mul_zero, zero_add, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum]
  have hc : d + ({i} ∪ T).card < n := by
    have hu := Finset.card_union_le ({i} : Point n) T
    simp only [Finset.card_singleton] at hu
    omega
  rw [total_degreeLE_monomial p hp _ hc, mul_zero]

lemma affine_orthogonal_of_indicator_degree {n d R : ℕ} (S : Finset (Point n))
    (p : BF n) (hp : DegreeLE p d) (hS : ∀ x, p x = if x ∈ S then 1 else 0)
    (hdeg : d + R + 1 < n) (c : ZMod 2) (b : Fin n → ZMod 2)
    (T : Point n) (hT : T.card ≤ R) :
    (∑ x ∈ S, affine c b x * monomial T x) = 0 := by
  have h := total_degreeLE_affine_monomial p hp c b T (by omega)
  simp_rw [hS] at h
  simp only [ite_mul, one_mul, zero_mul] at h
  simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using h

/-- Full-dimensional affine restriction theorem for any low-degree indicator
whose support lies in the two prescribed Hamming balls. -/
theorem restriction_affine_of_indicator_degree {n d R : ℕ}
    (S : Finset (Point n)) (p : BF n) (hp : DegreeLE p d)
    (hS : ∀ x, p x = if x ∈ S then 1 else 0) (hdeg : d + R + 1 < n)
    (hgeometry : ∀ x ∈ S, x.card ≤ 1 ∨ n - x.card ≤ R)
    (a : BF n)
    (horth : ∀ T : Point n, T.card ≤ R → (∑ x ∈ S, a x * monomial T x) = 0) :
    ∃ c : ZMod 2, ∃ b : Fin n → ZMod 2, ∀ x ∈ S, a x = affine c b x := by
  let c := a ∅
  let b : Fin n → ZMod 2 := fun i => a {i} - a ∅
  let z : BF n := fun x => a x - affine c b x
  have hlow : ∀ x : Point n, x.card ≤ 1 → z x = 0 := by
    intro x hx
    by_cases he : x = ∅
    · subst x
      simp [z, affine, c]
    · have hc : x.card = 1 := by
        have hh := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [z, affine, Finset.sum_singleton, c, b]
      ring
  have hz : ∀ T : Point n, T.card ≤ R → (∑ x ∈ S, z x * monomial T x) = 0 := by
    intro T hT
    simp only [z, sub_mul, Finset.sum_sub_distrib]
    rw [horth T hT, affine_orthogonal_of_indicator_degree S p hp hS hdeg c b T hT]
    simp
  refine ⟨c, b, ?_⟩
  intro x hx
  have h := restriction_zero_of_low_zero S z hgeometry hlow hz x hx
  exact sub_eq_zero.mp h

/-- The restriction step for the authors' family, valid in every dimension
where the already-proved support identity holds. -/
theorem family_restriction_affine {n : ℕ} (hn : 8 ≤ n)
    (hsupport : ∀ x : Point n, Fn n x = if x ∈ support n then 1 else 0)
    (a : BF n)
    (horth : ∀ T : Point n, T.card ≤ n/2-2 →
      (∑ x ∈ support n, a x * monomial T x) = 0) :
    ∃ c : ZMod 2, ∃ b : Fin n → ZMod 2, ∀ x ∈ support n, a x = affine c b x := by
  apply restriction_affine_of_indicator_degree (support n) (Fn n) (Fn_degree_le n)
    hsupport (by omega) (by intro x hx; exact (Finset.mem_filter.mp hx).2) a horth

end BentDecompositions.Family
