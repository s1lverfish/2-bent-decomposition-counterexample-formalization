module

public import BentDecomposition.B0Bent

@[expose] public section

namespace BentDecompositions.Family.ThreeSummands

/-- This is exactly the displayed sum identity, with addition in F₂. -/
theorem sum_eq_F8 (x : Point 8) : b0 x + b1 x + b2 x = F8 x := by
  simp only [b0]
  have h1 := ZModModule.add_self (b1 x)
  have h2 := ZModModule.add_self (b2 x)
  calc
    _ = F8 x + (b1 x+b1 x) + (b2 x+b2 x) := by ring
    _ = F8 x := by rw [h1,h2]; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem P_bijective : Function.Bijective P := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Q_bijective : Function.Bijective Q := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1_bent : Bent b1 := by
  unfold Bent walsh
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2_bent : Bent b2 := by
  unfold Bent walsh
  decide

theorem F8_three_bent : ∃ g0 g1 g2 : BF 8,
    Bent g0 ∧ Bent g1 ∧ Bent g2 ∧ ∀ x, g0 x+g1 x+g2 x=F8 x := by
  exact ⟨b0,b1,b2,b0_bent,b1_bent,b2_bent,sum_eq_F8⟩

/-- Existence of three summands and impossibility of fewer, on the same cube. -/
theorem F8_exactly_three :
    (∃ g0 g1 g2 : BF 8, Bent g0 ∧ Bent g1 ∧ Bent g2 ∧
      ∀ x, g0 x+g1 x+g2 x=F8 x) ∧ ¬ SumAtMostTwo F8 := by
  exact ⟨F8_three_bent,Fn_not_at_most_two 3 (by decide)⟩

#print axioms F8_three_bent
#print axioms F8_exactly_three
end BentDecompositions.Family.ThreeSummands
