module

public import BentDecomposition.Basic

@[expose] public section

namespace BentDecompositions.Family

variable {n : ℕ}

lemma character_prod (u x : Point n) :
    character u x = ∏ i ∈ u, (if i ∈ x then (-1 : ℤ) else 1) := by
  simp [character]

lemma monomial_fourier (T x : Point n) :
    ∑ u ∈ T.powerset, (-1 : ℤ)^u.card * character u x =
      2^T.card * (if T ⊆ x then 1 else 0) := by
  simp_rw [character_prod]
  have hp (u : Point n) :
      (-1 : ℤ)^u.card * (∏ i ∈ u, if i ∈ x then (-1 : ℤ) else 1) =
        ∏ i ∈ u, (if i ∈ x then (1 : ℤ) else -1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> norm_num
  simp_rw [hp]
  rw [← Finset.prod_one_add]
  by_cases ht : T ⊆ x
  · rw [ite_eq_left ht]
    have hprod : ∏ i ∈ T, (1 + if i ∈ x then (1 : ℤ) else -1) = ∏ i ∈ T, (2 : ℤ) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [ht hi]
    simp [hprod]
  · rw [ite_eq_right ht]
    simp only [mul_zero]
    obtain ⟨i, hi, hix⟩ := Finset.not_subset.mp ht
    apply Finset.prod_eq_zero hi
    simp [hix]

lemma sign_difference (a b : ZMod 2) (s : Prop) [Decidable s]
    (hab : a + b = if s then 1 else 0) :
    sign a - sign b = if s then 2 * sign a else 0 := by
  by_cases hs : s
  · simp only [ite_eq_left hs] at hab ⊢
    have hf : ∀ a b : ZMod 2, a + b = 1 → sign a - sign b = 2 * sign a := by decide
    exact hf a b hab
  · simp only [ite_eq_right hs] at hab ⊢
    have hf : ∀ a b : ZMod 2, a + b = 0 → sign a - sign b = 0 := by decide
    exact hf a b hab

lemma walsh_difference_identity (g h : BF n)
    (hgh : ∀ x, g x + h x = if x ∈ support n then 1 else 0) (T : Point n) :
    ∑ u ∈ T.powerset, (-1 : ℤ)^u.card * (walsh g u - walsh h u) =
      2^(T.card+1) * ∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0) := by
  calc
    _ = ∑ u ∈ T.powerset, ∑ x : Point n,
        (sign (g x) - sign (h x)) * ((-1 : ℤ)^u.card * character u x) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [walsh, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x : Point n, (sign (g x) - sign (h x)) *
        (∑ u ∈ T.powerset, (-1 : ℤ)^u.card * character u x) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ x : Point n, (if x ∈ support n then 2 * sign (g x) else 0) *
        (2^T.card * (if T ⊆ x then 1 else 0)) := by
      simp_rw [sign_difference _ _ _ (hgh _), monomial_fourier]
    _ = 2^(T.card+1) * ∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0) := by
      simp only [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, pow_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring

lemma bent_difference_dvd (g h : BF n) (hg : Bent g) (hh : Bent h) (u : Point n) :
    ((2 : ℤ) ^ (n/2+1)) ∣ walsh g u - walsh h u := by
  have hp : (2 : ℤ)^(n/2+1) = 2 * 2^(n/2) := by rw [pow_succ]; ring
  rw [hp]
  rcases hg u with hg | hg <;> rcases hh u with hh | hh <;> rw [hg, hh]
  · simp
  · exact ⟨1, by ring⟩
  · exact ⟨-1, by ring⟩
  · simp

/-- Full signed-support divisibility in arbitrary dimension. -/
theorem support_moment_dvd (g h : BF n) (hg : Bent g) (hh : Bent h)
    (hgh : ∀ x, g x + h x = if x ∈ support n then 1 else 0)
    (T : Point n) (ht : T.card ≤ n/2) :
    ((2 : ℤ)^(n/2-T.card)) ∣ ∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0) := by
  have hd : ((2 : ℤ)^(n/2+1)) ∣ ∑ u ∈ T.powerset,
      (-1 : ℤ)^u.card * (walsh g u - walsh h u) := by
    apply Finset.dvd_sum
    intro u hu
    exact dvd_mul_of_dvd_right (bent_difference_dvd g h hg hh u) _
  rw [walsh_difference_identity g h hgh T] at hd
  have he : n/2+1 = (T.card+1)+(n/2-T.card) := by omega
  rw [he, pow_add] at hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero (T.card+1) (by norm_num : (2 : ℤ) ≠ 0))).mp hd

/-- The divisibility by four used in the orthogonality step. -/
theorem support_moment_dvd_four (g h : BF n) (hg : Bent g) (hh : Bent h)
    (hgh : ∀ x, g x + h x = if x ∈ support n then 1 else 0)
    (T : Point n) (hn : 4 ≤ n) (ht : T.card ≤ n/2-2) :
    (4 : ℤ) ∣ ∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0) := by
  have hm : T.card ≤ n/2 := by omega
  have he : n/2-T.card = 2+(n/2-T.card-2) := by omega
  have hfour : (4 : ℤ) ∣ (2 : ℤ)^(n/2-T.card) := by
    rw [he, pow_add]
    norm_num
  exact dvd_trans hfour (support_moment_dvd g h hg hh hgh T hm)

lemma sign_finset_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

lemma character_comm (u x : Point n) : character u x = character x u := by
  simp [character, Finset.inter_comm]

lemma sign_affine (c : ZMod 2) (b : Fin n → ZMod 2) (x : Point n) :
    sign (affine c b x) = sign c * character (Finset.univ.filter (fun i => b i = 1)) x := by
  simp only [affine, sign_add, sign_finset_sum]
  rw [character_comm, character_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hf : ∀ a : ZMod 2, sign a = if a = 1 then (-1 : ℤ) else 1 := by decide
  exact hf (b i)

lemma walsh_difference_support (g h : BF n)
    (hgh : ∀ x, g x + h x = if x ∈ support n then 1 else 0) (u : Point n) :
    walsh g u - walsh h u = 2 * ∑ x ∈ support n, sign (g x) * character u x := by
  simp only [walsh, ← Finset.sum_sub_distrib, ← sub_mul]
  simp_rw [sign_difference _ _ _ (hgh _)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

open scoped symmDiff

private theorem sign_nat (n : ℕ) : sign (n : ZMod 2) = (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_add, sign_add, ih, pow_succ]

def linear (u x : Point n) : ZMod 2 := ∑ i ∈ x, if i ∈ u then 1 else 0

theorem character_eq_sign_linear (u x : Point n) : character u x = sign (linear u x) := by
  have h : linear u x = ((u ∩ x).card : ZMod 2) := by
    simp only [linear, Finset.sum_boole]
    congr 1
    congr 1
    ext i
    simp [and_comm]
  rw [h, sign_nat]
  rfl

theorem linear_symmDiff (u v x : Point n) : linear (u ∆ v) x = linear u x + linear v x := by
  unfold linear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hu : i ∈ u <;> by_cases hv : i ∈ v <;>
    norm_num [Finset.mem_symmDiff, hu, hv]; decide

theorem character_symmDiff (u v x : Point n) :
    character (u ∆ v) x = character u x * character v x := by
  simp only [character_eq_sign_linear, linear_symmDiff, sign_add]

theorem affine_eq_linear (c : ZMod 2) (b : Fin n → ZMod 2) (x : Point n) :
    affine c b x = c + linear (Finset.univ.filter (fun i => b i = 1)) x := by
  unfold affine linear
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have bit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases bit (b i) with hz | hz <;> simp [hz]

/-- Adding an affine output shifts the Walsh frequency and changes only its sign. -/
theorem walsh_affine (f : BF n) (c : ZMod 2) (b : Fin n → ZMod 2) (u : Point n) :
    walsh (fun x => f x + affine c b x) u =
      sign c * walsh f (u ∆ Finset.univ.filter (fun i => b i = 1)) := by
  unfold walsh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  change sign (f x + affine c b x) * character u x = _
  rw [affine_eq_linear, sign_add, sign_add, ← character_eq_sign_linear,
    character_symmDiff]
  ring

/-- Affine output perturbations preserve bentness, with no assumption on the summand. -/
theorem bent_add_affine {f : BF n} (hf : Bent f) (c : ZMod 2) (b : Fin n → ZMod 2) :
    Bent (fun x => f x + affine c b x) := by
  intro u
  rw [walsh_affine]
  rcases hf (u ∆ Finset.univ.filter (fun i => b i = 1)) with h | h <;>
    rw [h] <;> by_cases hc : c = 0 <;> simp [sign, hc]



/-- The signed count equals the support size minus twice its one-set size. -/
lemma sum_sign_eq_card_sub_twice {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ZMod 2) :
    (∑ x ∈ S, sign (f x)) = (S.card : ℤ) - 2 * ((S.filter (fun x => f x = 1)).card : ℤ) := by
  have hb : ∀ z : ZMod 2, sign z = 1 - 2 * (if z = 1 then (1 : ℤ) else 0) := by decide
  simp_rw [hb]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- Normalized bent summands force the authors' weight discrepancy to be divisible
by the bent Walsh magnitude. Counts can be supplied independently. -/
theorem normalized_discrepancy_dvd (g h : BF n) (hg : Bent g) (hh : Bent h)
    (hgh : ∀ x, g x + h x = if x ∈ support n then 1 else 0)
    (hnorm : ∀ x ∈ support n, g x = delta x) :
    ((2 : ℤ)^(n/2)) ∣ ((support n).card : ℤ) -
      2 * (((support n).filter (fun x => delta x = 1)).card : ℤ) := by
  have hw : walsh g ∅ - walsh h ∅ = 2 *
      (((support n).card : ℤ) - 2 * (((support n).filter (fun x => delta x = 1)).card : ℤ)) := by
    rw [walsh_difference_support g h hgh]
    simp only [character_empty, mul_one]
    congr 1
    calc
      _ = ∑ x ∈ support n, sign (delta x) := Finset.sum_congr rfl (fun x hx => congrArg sign (hnorm x hx))
      _ = _ := sum_sign_eq_card_sub_twice (support n) delta
  have hd := bent_difference_dvd g h hg hh ∅
  rw [hw, pow_succ] at hd
  have hc : ((2 : ℤ)^(n/2)) * 2 = 2 * 2^(n/2) := by ring
  rw [hc] at hd
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hd

/-- Arithmetic endpoint: a discrepancy four modulo eight cannot satisfy the
necessary bent-magnitude divisibility when n/2≥3. -/
theorem discrepancy_contradiction (D : ℤ) (hm : 3 ≤ n/2)
    (hd : ((2 : ℤ)^(n/2)) ∣ D) (hmod : D % 8 = 4) : False := by
  have hp : (8 : ℤ) ∣ (2 : ℤ)^(n/2) := by
    have he : n/2 = 3 + (n/2-3) := by omega
    rw [he, pow_add]
    norm_num
  have hzero := Int.emod_eq_zero_of_dvd (dvd_trans hp hd)
  omega


def bitValue (z : ZMod 2) : ℤ := if z = 0 then 0 else 1

lemma sign_eq_one_sub (z : ZMod 2) : sign z = 1 - 2 * bitValue z := by
  revert z; decide

@[simp] lemma cast_bitValue (z : ZMod 2) : (bitValue z : ZMod 2) = z := by
  revert z; decide

/-- Convert signed-count divisibility and a count congruence into mod-two
orthogonality, without specializing the dimension or the target count. -/
theorem parity_from_divisibility (g : BF n) (T : Point n) (I : ℤ)
    (hcount : (((support n).filter (fun x => T ⊆ x)).card : ℤ) % 4 = (2*I) % 4)
    (hdiv : (4 : ℤ) ∣ ∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0)) :
    (∑ x ∈ support n, g x * monomial T x) = (I : ZMod 2) := by
  let selected := (support n).filter (fun x => T ⊆ x)
  let Z : ℤ := ∑ x ∈ selected, bitValue (g x)
  have hid : (∑ x ∈ support n, sign (g x) * (if T ⊆ x then 1 else 0)) =
      (selected.card : ℤ) - 2 * Z := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    change (∑ x ∈ selected, sign (g x)) = _
    simp_rw [sign_eq_one_sub]
    simp [Finset.sum_sub_distrib, Finset.mul_sum, Z]
  rw [hid] at hdiv
  have hZ : Z % 2 = I % 2 := by
    change (selected.card : ℤ) % 4 = (2*I) % 4 at hcount
    obtain ⟨q, hq⟩ := hdiv
    omega
  have hcast : (Z : ZMod 2) = (I : ZMod 2) :=
    (ZMod.intCast_eq_intCast_iff' Z I 2).mpr hZ
  have hsum : (Z : ZMod 2) = ∑ x ∈ support n, g x * monomial T x := by
    simp only [Z, Int.cast_sum, cast_bitValue]
    simp [selected, monomial, Finset.sum_filter, mul_ite]
  rw [← hsum]
  exact hcast

end BentDecompositions.Family
