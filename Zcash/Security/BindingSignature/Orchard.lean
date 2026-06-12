import Zcash.Security.BindingSignature.Balance

/-!
# Orchard no-overflow bound (spec §4.14)

The Orchard action count is bounded *directly* by a dedicated consensus rule `n ≤ 2^16 − 1`,
independent of the transaction size (the spec notes this is technically redundant given the 2 MB
limit, but it stands on its own — the elegant case). Each action commits to the signed *net* value
`v = v_spend − v_output`, range-proven by the Action statement to lie in
`SignedValueDifferenceType = [−2^64+1, 2^64−1]`, i.e. `|v| ≤ 2^64 − 1`.

This module instantiates the generic `natAbs_lt_of_abs_le` from `Balance` at those concrete bounds,
discharging the `hbound` hypothesis of `bundle_integer_balances` for Orchard.
-/

namespace Zcash.Security.BindingSignature

/-- The Pallas scalar field order `r_ℙ` — the order of the Pallas group, which is the scalar field of
the Orchard value commitment (spec § Pallas and Vesta). -/
def pallasScalarOrder : ℕ := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- The Orchard `vSum` magnitude bound = the spec's `ValueCommitTypeOrchard` subrange endpoint:
`(2^16 − 1)·(2^64 − 1) + 2^63`, from `|v| ≤ 2^64 − 1` per action and the consensus rule `n ≤ 2^16 − 1`
(plus the signed-64-bit `vBalance`). -/
def orchardVSumBound : ℤ := (2^16 - 1) * (2^64 - 1) + 2^63

/-- The bound equals the spec's quoted endpoint. -/
example : orchardVSumBound = 1208916596242592319864833 := by norm_num [orchardVSumBound]

/-- **Orchard no-overflow bound.** With `|v| ≤ 2^64 − 1` per action, `n ≤ 2^16 − 1` actions, and
`|vBalance| ≤ 2^63`, the net sum `vSum = ∑ v − vBalance` has `vSum.natAbs < r` once
`orchardVSumBound < r`. This is the `hbound` of `bundle_integer_balances` for Orchard. -/
theorem orchard_natAbs_lt {r : ℕ} (vs : List ℤ) (vBalance : ℤ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ 2^16 - 1)
    (hvb : |vBalance| ≤ 2^63)
    (hr : orchardVSumBound < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r := by
  refine natAbs_lt_of_abs_le ?_ hr
  have hlen : (vs.length : ℤ) ≤ 2^16 - 1 := by norm_num at hn ⊢; exact_mod_cast hn
  have hs : |vs.sum| ≤ (2^16 - 1) * (2^64 - 1) :=
    le_trans (abs_listSum_le hv) (mul_le_mul_of_nonneg_right hlen (by norm_num))
  calc |vs.sum - vBalance| ≤ |vs.sum| + |vBalance| := abs_sub _ _
    _ ≤ (2^16 - 1) * (2^64 - 1) + 2^63 := add_le_add hs hvb
    _ = orchardVSumBound := by norm_num [orchardVSumBound]

/-- The gap holds for the Pallas scalar field, so `orchard_natAbs_lt` is not vacuous. -/
example : orchardVSumBound < (pallasScalarOrder : ℤ) := by
  norm_num [orchardVSumBound, pallasScalarOrder]

end Zcash.Security.BindingSignature
