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

/-- Assemble the two four-coordinate blocks. -/
def join (X Y : Four) : Point 8 := Finset.univ.filter fun i =>
  if h : i.val < 4 then (⟨i.val,h⟩ : Fin 4) ∈ X
  else (⟨i.val-4,by omega⟩ : Fin 4) ∈ Y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem join_card : ∀ X Y : Four, (join X Y).card = X.card + Y.card := by decide

private theorem lower_join (X Y : Four) : lower (join X Y) = X := by
  ext i
  simp [lower, join]

private theorem upper_join (X Y : Four) : upper (join X Y) = Y := by
  ext i
  simp [upper, join]

private theorem join_blocks (x : Point 8) : join (lower x) (upper x) = x := by
  ext i
  fin_cases i <;> simp [join,lower,upper]

private theorem inter_join (u : Point 8) (X Y : Four) :
    u ∩ join X Y = join (lower u ∩ X) (upper u ∩ Y) := by
  ext i
  fin_cases i <;> simp [join,lower,upper]

private theorem character_join (u : Point 8) (X Y : Four) :
    character u (join X Y) = character (lower u) X * character (upper u) Y := by
  simp only [character, inter_join, join_card, pow_add]

private def blocks : Point 8 ≃ Four × Four where
  toFun x := (lower x, upper x)
  invFun p := join p.1 p.2
  left_inv := join_blocks
  right_inv p := by simp only [lower_join,upper_join]

private theorem sum_blocks (f : Point 8 → ℤ) :
    ∑ x, f x = ∑ X : Four, ∑ Y : Four, f (join X Y) := by
  calc
    _ = ∑ p : Four × Four, f (join p.1 p.2) :=
      Fintype.sum_equiv blocks f (fun p => f (join p.1 p.2))
        (fun x => by rw [show join (blocks x).1 (blocks x).2 = x from join_blocks x])
    _ = _ := Fintype.sum_prod_type _

/-- The symmetric F8 slice when the first block has weight a. -/
private def slice (a : ℕ) (Y : Four) : ZMod 2 :=
  if a + Y.card ≤ 1 ∨ 6 ≤ a + Y.card then 1 else 0

private theorem F8_join (X Y : Four) : F8 (join X Y) = slice X.card Y := by
  have hs : (join X Y ∈ support 8) ↔
      (X.card + Y.card ≤ 1 ∨ 6 ≤ X.card + Y.card) := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, join_card]
    omega
  change Fn 8 (join X Y) = _
  rw [show Fn 8 (join X Y) = (if join X Y ∈ support 8 then 1 else 0) from
    Fn_eq_indicator 3 (by decide) (join X Y)]
  simp only [hs, slice]

private theorem b0_join (X Y : Four) :
    b0 (join X Y) = slice X.card Y + dot Y (P X) + dot Y (Q X) + r X := by
  simp only [b0,b1,b2,F8_join,lower_join,upper_join]
  ring

/-- Five slice weights by five frequency weights, in ordinary integers. -/
private def sliceSpectrum (a t : ℕ) : ℤ :=
  (([[6,-6,-2,2,6], [14,-2,-2,-2,-2], [14,2,-2,2,-2],
     [6,6,-2,-2,6], [-6,6,2,-2,-6]] : List (List ℤ)).getD a []).getD t 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem slice_transform : ∀ (a : Fin 5) (v : Four),
    (∑ Y : Four, sign (slice a.val Y) * character v Y) = sliceSpectrum a.val v.card := by
  decide

private theorem sign_dot (u x : Four) : sign (dot u x) = character u x := by
  revert u x
  decide

open scoped symmDiff

private theorem section_transform (X v : Four) :
    (∑ Y : Four, sign (slice X.card Y + dot Y (P X) + dot Y (Q X) + r X) * character v Y) =
      sign (r X) * sliceSpectrum X.card (v ∆ P X ∆ Q X).card := by
  have hc : X.card < 5 := by
    have h : X.card ≤ 4 := by simpa using Finset.card_le_univ X
    omega
  have hs := slice_transform ⟨X.card,hc⟩ (v ∆ P X ∆ Q X)
  rw [← hs]
  change (∑ Y : Four, _) = sign (r X) * (∑ Y : Four, sign (slice X.card Y) * character (v ∆ P X ∆ Q X) Y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  simp only [sign_add, sign_dot, character_symmDiff]
  rw [character_comm Y (P X), character_comm Y (Q X)]
  ring

/-- Only sixteen terms remain after the Y-slice transform. -/
private def reducedWalsh (A B : Four) : ℤ :=
  ∑ X : Four, character A X * sign (r X) *
    sliceSpectrum X.card (B ∆ P X ∆ Q X).card

private theorem walsh_b0_reduced (u : Point 8) :
    walsh b0 u = reducedWalsh (lower u) (upper u) := by
  unfold walsh
  rw [sum_blocks]
  simp_rw [character_join]
  calc
    _ = ∑ X : Four, character (lower u) X *
        (∑ Y : Four, sign (b0 (join X Y)) * character (upper u) Y) := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y hY
      ring
    _ = _ := by
      simp_rw [b0_join, section_transform]
      simp only [reducedWalsh, mul_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem reduced_bent : ∀ A B : Four,
    reducedWalsh A B = 16 ∨ reducedWalsh A B = -16 := by decide

/-- Bentness checked through a five-by-five slice table and sixteen-term sums. -/
theorem b0_bent : Bent b0 := by
  intro u
  change walsh b0 u = 16 ∨ walsh b0 u = -16
  rw [walsh_b0_reduced]
  exact reduced_bent (lower u) (upper u)

#print axioms b0_bent
end BentDecompositions.Family.ThreeSummands
