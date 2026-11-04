module

public import BentDecomposition.Main

@[expose] public section

namespace BentDecompositions.Family.ThreeSummands

abbrev Four := Finset (Fin 4)

/-- The eight-variable member of the existing infinite family. -/
abbrev F8 : BF 8 := Fn 8

def lower (x : Point 8) : Four := Finset.univ.filter (fun i => (⟨i.val, by omega⟩ : Fin 8) ∈ x)
def upper (x : Point 8) : Four := Finset.univ.filter (fun i => (⟨i.val+4, by omega⟩ : Fin 8) ∈ x)

/-- Internal encoding: (x1,x2,x3,x4) has code x1+2*x2+4*x3+8*x4. -/
def code (x : Four) : ℕ := ∑ i ∈ x, 2^i.val
def vector (j : ℕ) : Four := Finset.univ.filter (fun i => j.testBit i.val)

def P (x : Four) : Four := vector (([0,1,2,4,6,7,9,5,10,12,3,8,15,11,13,14] : List ℕ).getD (code x) 0)
def Q (x : Four) : Four := vector (([0,10,12,7,15,2,3,5,6,1,4,8,9,11,13,14] : List ℕ).getD (code x) 0)

def r (x : Four) : ZMod 2 := if code x = 9 ∨ code x = 10 ∨ code x = 15 then 0 else 1

def dot (x y : Four) : ZMod 2 := ((x ∩ y).card : ZMod 2)

def b1 (x : Point 8) : ZMod 2 := dot (upper x) (P (lower x))
def b2 (x : Point 8) : ZMod 2 := dot (upper x) (Q (lower x)) + r (lower x)
def b0 (x : Point 8) : ZMod 2 := F8 x + b1 x + b2 x

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
theorem b0_bent : Bent b0 := by
  have h0 : b0 = fun x => (if x ∈ support 8 then 1 else 0) + b1 x + b2 x := by
    funext x
    exact congrArg (fun z : ZMod 2 => z + b1 x + b2 x)
      (Fn_eq_indicator 3 (by decide) x)
  rw [h0]
  unfold Bent walsh
  decide

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
