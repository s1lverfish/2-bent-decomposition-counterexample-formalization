module

public import BentDecomposition.Signs

@[expose] public section

namespace BentDecompositions.Family

abbrev Point (n : ℕ) := Finset (Fin n)
abbrev BF (n : ℕ) := Point n → ZMod 2

def character {n : ℕ} (u x : Point n) : ℤ := (-1) ^ (u ∩ x).card

def walsh {n : ℕ} (f : BF n) (u : Point n) : ℤ :=
  ∑ x : Point n, sign (f x) * character u x

def Bent {n : ℕ} (f : BF n) : Prop :=
  ∀ u, walsh f u = (2 : ℤ)^(n/2) ∨ walsh f u = -((2 : ℤ)^(n/2))

def monomial {n : ℕ} (T x : Point n) : ZMod 2 := if T ⊆ x then 1 else 0

def affine {n : ℕ} (c : ZMod 2) (b : Fin n → ZMod 2) (x : Point n) : ZMod 2 :=
  c + ∑ i ∈ x, b i

def evalANF {n : ℕ} (a : Point n → ZMod 2) (x : Point n) : ZMod 2 :=
  ∑ T : Point n, a T * monomial T x

def DegreeLE {n : ℕ} (f : BF n) (d : ℕ) : Prop :=
  ∃ a : Point n → ZMod 2, (∀ T, d < T.card → a T = 0) ∧ f = evalANF a

/-- Coefficients of the authors' symmetric polynomial in arbitrary dimension. -/
def familyCoefficients (n : ℕ) (T : Point n) : ZMod 2 :=
  if Even T.card ∧ T.card ≤ n/2 then 1 else 0

def Fn (n : ℕ) : BF n := evalANF (familyCoefficients n)

def support (n : ℕ) : Finset (Point n) :=
  Finset.univ.filter (fun x => x.card ≤ 1 ∨ n - x.card ≤ n/2-2)

def delta {n : ℕ} (x : Point n) : ZMod 2 :=
  if n - x.card ≤ n/4-2 then 1 else 0

/-- Partial binomial sum, with choose(a,j)=0 when a<j. -/
def P (a b : ℕ) : ℕ := ∑ j ∈ Finset.range (b+1), Nat.choose a j

@[simp] theorem character_empty {n : ℕ} (x : Point n) : character ∅ x = 1 := by
  simp [character]

theorem Fn_degree_le (n : ℕ) : DegreeLE (Fn n) (n/2) := by
  refine ⟨familyCoefficients n, ?_, rfl⟩
  intro T hT
  simp [familyCoefficients, show ¬ T.card ≤ n/2 by omega]

end BentDecompositions.Family
