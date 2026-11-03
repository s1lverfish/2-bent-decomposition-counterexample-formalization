module

public import BentDecomposition.Geometry
public import BentDecomposition.WalshSupport

@[expose] public section

namespace BentDecompositions.Family

/-- Exact support of the authors' polynomial in every dyadic dimension. -/
theorem Fn_eq_indicator (k : ℕ) (hk : 3 ≤ k) (x : Point (2^k)) :
    Fn (2^k) x = if x ∈ support (2^k) then 1 else 0 := by
  have he : k = (k-2)+2 := by omega
  have hn : 2^k = 4*2^(k-2) := by
    calc
      2^k = 2^((k-2)+2) := congrArg (fun e : ℕ => 2^e) he
      _ = 4*2^(k-2) := by rw [pow_add]; norm_num; omega
  have hh : 2^k/2 = 2*2^(k-2) := by omega
  have hw : x.card ≤ 2^k := by simpa using Finset.card_le_univ x
  have hp : 2 ≤ 2^(k-2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k-2)
  rw [Fn_weight_formula, hh, scalar_support_parity_even _ _ (by omega)]
  have hmem : x ∈ support (2^k) ↔ x.card ≤ 1 ∨ 2^k-x.card ≤ 2^k/2-2 := by
    simp [support]
  have hiff : (x.card ≤ 1 ∨ 2*2^(k-2)+2 ≤ x.card) ↔ x ∈ support (2^k) := by
    rw [hmem]
    omega
  exact if_congr hiff rfl rfl

end BentDecompositions.Family
