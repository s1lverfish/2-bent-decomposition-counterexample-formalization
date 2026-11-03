module

public import BentDecomposition.Basic

@[expose] public section

namespace BentDecompositions.Family

def upperBall (n R : ℕ) : Finset (Point n) :=
  Finset.univ.filter (fun x => n-x.card ≤ R)

def lowerBall (n : ℕ) : Finset (Point n) :=
  Finset.univ.filter (fun x => x.card ≤ 1)

def downBall {n : ℕ} (s : Point n) (R : ℕ) : Finset (Point n) :=
  s.powerset.filter (fun x => x.card ≤ R)

/-- Count the small subsets by their cardinalities. -/
theorem downBall_card {n : ℕ} (s : Point n) (R : ℕ) :
    (downBall s R).card = P s.card R := by
  have hm : Set.MapsTo (fun x : Point n => x.card)
      (downBall s R) (Finset.range (R+1)) := by
    intro x hx
    exact Finset.mem_range.mpr (by simpa [downBall] using (Finset.mem_filter.mp hx).2)
  rw [Finset.card_eq_sum_card_fiberwise hm]
  unfold P
  apply Finset.sum_congr rfl
  intro j hj
  have hset : (downBall s R).filter (fun x => x.card = j) = s.powersetCard j := by
    ext x
    have hjR : j ≤ R := by simpa using hj
    simp only [downBall, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hs, hR⟩, hc⟩
      exact ⟨hs, hc⟩
    · rintro ⟨hs, rfl⟩
      exact ⟨⟨hs, hjR⟩, rfl⟩
  rw [hset, Finset.card_powersetCard]

/-- Group a symmetric ANF by its monomial degree. -/
theorem Fn_weight_formula (n : ℕ) (x : Point n) :
    Fn n x = ∑ j ∈ Finset.range (n/2+1),
      if Even j then (Nat.choose x.card j : ZMod 2) else 0 := by
  let A : Finset (Point n) := Finset.univ.filter (fun T => T.card ≤ n/2)
  have hA : Set.MapsTo (fun T : Point n => T.card) A (Finset.range (n/2+1)) := by
    intro T hT
    have hb : T.card ≤ n/2 := (Finset.mem_filter.mp hT).2
    exact Finset.mem_range.mpr (by change T.card < n/2+1; omega)
  have hstart : Fn n x = ∑ T ∈ A, (if Even T.card then (1 : ZMod 2) else 0) * monomial T x := by
    unfold Fn evalANF familyCoefficients
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases he : Even T.card <;> by_cases hb : T.card ≤ n/2 <;> simp [he, hb]
  rw [hstart, ← Finset.sum_fiberwise_of_maps_to hA]
  apply Finset.sum_congr rfl
  intro j hj
  have hjR : j ≤ n/2 := by simpa using hj
  calc
    _ = ∑ T : Point n, if T.card = j ∧ T ⊆ x then
        (if Even j then (1 : ZMod 2) else 0) else 0 := by
      simp only [Finset.sum_filter, A, monomial]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hc : T.card = j
      · subst j
        simp [hjR]
      · simp [hc]
    _ = if Even j then (((x.powersetCard j).card : ℕ) : ZMod 2) else 0 := by
      by_cases he : Even j
      · simp only [he, ite_true]
        have hset : Finset.univ.filter (fun T : Point n => T.card = j ∧ T ⊆ x) =
            x.powersetCard j := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
          tauto
        rw [← Finset.sum_filter]
        simp [hset]
      · simp [he]
    _ = _ := by rw [Finset.card_powersetCard]

@[simp] theorem point_card_compl {n : ℕ} (x : Point n) :
    xᶜ.card = n - x.card := by
  exact (Finset.card_compl x).trans (by rw [Fintype.card_fin])

theorem upper_selected_card (n R : ℕ) (T : Point n) :
    ((upperBall n R).filter (fun x => T ⊆ x)).card = P (n-T.card) R := by
  have hb : ((upperBall n R).filter (fun x => T ⊆ x)).card =
      (downBall Tᶜ R).card := by
    apply Finset.card_bij (fun x _ => xᶜ)
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hx, hT⟩
      have hr : n-x.card ≤ R := (Finset.mem_filter.mp hx).2
      simp only [downBall, Finset.mem_filter, Finset.mem_powerset, point_card_compl]
      exact ⟨Finset.compl_subset_compl.mpr hT, hr⟩
    · intro x hx y hy hxy
      simpa using congrArg (fun z : Point n => zᶜ) hxy
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyT, hyR⟩
      have hyT' : y ⊆ Tᶜ := Finset.mem_powerset.mp hyT
      have hsub : T ⊆ yᶜ := by
        simpa using Finset.compl_subset_compl.mpr hyT'
      have hc : n-yᶜ.card = y.card := by
        simpa using (point_card_compl yᶜ).symm
      refine ⟨yᶜ, ?_, by simp⟩
      simp only [Finset.mem_filter, upperBall, Finset.mem_univ, true_and, hc]
      exact ⟨hyR, hsub⟩
  rw [hb, downBall_card, point_card_compl]

theorem lowerBall_card (n : ℕ) : (lowerBall n).card = n+1 := by
  have hb : lowerBall n = downBall (Finset.univ : Point n) 1 := by
    ext x
    simp [lowerBall, downBall]
  rw [hb, downBall_card]
  simp [P, Finset.sum_range_succ, add_comm]

def lowerCorrection (n t : ℕ) : ℕ := if t=0 then n+1 else if t=1 then 1 else 0

theorem lower_selected_card (n : ℕ) (T : Point n) :
    ((lowerBall n).filter (fun x => T ⊆ x)).card = lowerCorrection n T.card := by
  by_cases h0 : T.card = 0
  · have ht : T = ∅ := Finset.card_eq_zero.mp h0
    subst T
    simp [lowerCorrection, lowerBall_card]
  · by_cases h1 : T.card = 1
    · have hs : (lowerBall n).filter (fun x => T ⊆ x) = {T} := by
        ext x
        simp only [Finset.mem_filter, lowerBall, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hsub⟩
          exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
        · rintro rfl
          exact ⟨by omega, Finset.Subset.refl _⟩
      simp [hs, lowerCorrection, h1]
    · have hs : (lowerBall n).filter (fun x => T ⊆ x) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hx, hsub⟩
        have hc : x.card ≤ 1 := (Finset.mem_filter.mp hx).2
        have hle := Finset.card_le_card hsub
        omega
      simp [hs, lowerCorrection, h0, h1]

theorem support_eq_union (n : ℕ) :
    support n = lowerBall n ∪ upperBall n (n/2-2) := by
  ext x
  simp [support, lowerBall, upperBall]

theorem balls_disjoint (n : ℕ) (hn : 8 ≤ n) :
    Disjoint (lowerBall n) (upperBall n (n/2-2)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hl : x.card ≤ 1 := (Finset.mem_filter.mp hx).2
  have hu : n-x.card ≤ n/2-2 := (Finset.mem_filter.mp hy).2
  omega

theorem support_selected_card (n : ℕ) (hn : 8 ≤ n) (T : Point n) :
    ((support n).filter (fun x => T ⊆ x)).card =
      P (n-T.card) (n/2-2) + lowerCorrection n T.card := by
  rw [support_eq_union, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (balls_disjoint n hn)),
    lower_selected_card, upper_selected_card]
  omega

theorem support_card (n : ℕ) (hn : 8 ≤ n) :
    (support n).card = P n (n/2-2) + n + 1 := by
  have h := support_selected_card n hn ∅
  simpa [lowerCorrection, add_assoc] using h

theorem delta_selected_sum (n : ℕ) (T : Point n) :
    (∑ x ∈ support n, delta x * monomial T x) =
      (P (n-T.card) (n/4-2) : ZMod 2) := by
  have hr : n/4-2 ≤ n/2-2 := by omega
  have hset : (support n).filter (fun x => n-x.card ≤ n/4-2 ∧ T ⊆ x) =
      (upperBall n (n/4-2)).filter (fun x => T ⊆ x) := by
    ext x
    simp only [support, upperBall, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hs, hδ, hT⟩
      exact ⟨hδ, hT⟩
    · rintro ⟨hδ, hT⟩
      exact ⟨Or.inr (by omega), hδ, hT⟩
  calc
    _ = ∑ x ∈ support n, if n-x.card ≤ n/4-2 ∧ T ⊆ x then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hδ : n-x.card ≤ n/4-2 <;> by_cases hT : T ⊆ x <;>
        simp [delta, monomial, hδ, hT]
    _ = (((support n).filter (fun x => n-x.card ≤ n/4-2 ∧ T ⊆ x)).card : ZMod 2) := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by rw [hset, upper_selected_card]

theorem delta_card (n : ℕ) :
    ((support n).filter (fun x => delta x = 1)).card = P n (n/4-2) := by
  have hr : n/4-2 ≤ n/2-2 := by omega
  have hset : (support n).filter (fun x => delta x = 1) = upperBall n (n/4-2) := by
    ext x
    constructor
    · intro hx
      have hδ : delta x = 1 := (Finset.mem_filter.mp hx).2
      have hp : n-x.card ≤ n/4-2 := by
        by_contra hneg
        simp only [delta, ite_eq_right hneg] at hδ
        exact zero_ne_one hδ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · intro hx
      have hp : n-x.card ≤ n/4-2 := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inr (by omega)⟩, by simp [delta, hp]⟩
  rw [hset]
  have h := upper_selected_card n (n/4-2) ∅
  simpa using h

end BentDecompositions.Family
