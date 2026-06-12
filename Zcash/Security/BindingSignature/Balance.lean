import Mathlib

/-!
# Binding-signature balance: shared algebraic core

This module formalizes the algebraic heart of the Zcash binding-signature *balance* argument
(Zcash protocol specification §4.13 Sapling / §4.14 Orchard), abstracted over an arbitrary
`F`-module `M` so that it applies to both the Jubjub (Sapling) and Pallas (Orchard)
value-commitment groups. Here `F` will be instantiated with the scalar field `ZMod r`.

## The setting

Value commitments are `cv v rcv = v • V + rcv • R` for fixed generators `V` (value base) and
`R` (randomness base). For a bundle, the binding verification key is
`bvk = (∑ spend cv) − (∑ output cv) − v_balance • V`, which by homomorphicity equals
`A • V + B • R`, where `A = ∑ v_in − ∑ v_out − v_balance` and `B = ∑ rcv_in − ∑ rcv_out`.

## How binding is expressed (and why not as "no relation exists")

In a prime-order group, `V` and `R` are *always* discrete-log-related — a nontrivial `(a,b)` with
`a • V + b • R = 0` exists; you simply cannot *find* it. So the information-theoretic statement
"the only relation is trivial" is **false** in the group setting and must not be used as the
binding hypothesis. Instead we phrase binding as a **reduction**:

* `§ Group-faithful` below proves, with *no* cryptographic hypothesis, that a non-balancing
  verifying bundle **exhibits** an explicit nontrivial relation between `V` and `R`
  (`relation_of_imbalance`), equivalently the discrete log `dlog_R V` (`rand_log_of_imbalance`).
  "The bundle balances" is then the *contrapositive under discrete-log-relation hardness* — a
  statement about efficient adversaries, supplied by the algebraic group model or a DLR-hardness
  assumption at the computational layer. This is the shape of the spec's argument: *if you can
  unbalance, you can solve DL.*

* `§ Abstract model` keeps the information-theoretic `Binding` predicate, but only as a sanity
  check over a *general* `F`-module where `V, R` genuinely can be independent (e.g. a rank-≥2 free
  module). It is **not** the group assumption and is never instantiated at a prime-order group.

## Assumptions / later steps

* **RedDSA extractability** (`bvk = bsk • R` from a verifying binding signature) — assumed, not
  proved (its proof needs a random oracle + forking); supplied as the `hExtract` hypothesis.
* **Discrete-log-relation hardness** — discharges the reduction above to actual balance; lives in
  the computational/AGM layer (not yet built).
* **Lifting `A = 0` in `F = ZMod r` to integer balance** (`∑ v_in = ∑ v_out + v_balance` over ℤ) —
  the range / no-overflow argument (`intBalance_eq_zero_of_lt`, valid when `MAX_MONEY · maxActions <
  r`); wiring it to the homomorphic-sum layer is the remaining piece.
-/

namespace Zcash.Security.BindingSignature

variable {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- From RedDSA extractability (`bvk = bsk • R`) and the homomorphic decomposition of the binding
verification key (`bvk = A • V + B • R`), the value coefficient satisfies `A • V = (bsk − B) • R`.
True unconditionally (pure module algebra). -/
theorem smul_value_eq_smul_rand (V R bvk : M) (A B bsk : F)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A • V = (bsk - B) • R := by
  have h : A • V + B • R = bsk • R := by rw [← hSum, hExtract]
  calc A • V = bsk • R - B • R := eq_sub_of_add_eq h
    _ = (bsk - B) • R := (sub_smul bsk B R).symm

/-! ### Group-faithful reduction (no cryptographic hypothesis; true in a prime-order group) -/

/-- **The group-faithful binding reduction.** A non-balancing (`A ≠ 0`) verifying bundle *exhibits*
an explicit nontrivial discrete-log relation between the value base `V` and the randomness base `R`:
the coefficients `(A, B − bsk)` are not both zero (indeed `A ≠ 0`) and `A • V + (B − bsk) • R = 0`.
Such a relation always exists in the group; the content is that imbalance *produces* one — which,
under discrete-log-relation hardness, cannot happen, so the bundle balances. -/
theorem relation_of_imbalance (V R bvk : M) (A B bsk : F)
    (hA : A ≠ 0)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A ≠ 0 ∧ A • V + (B - bsk) • R = 0 := by
  refine ⟨hA, ?_⟩
  rw [smul_value_eq_smul_rand V R bvk A B bsk hExtract hSum, ← add_smul]
  have hc : (bsk - B) + (B - bsk) = (0 : F) := by ring
  rw [hc, zero_smul]

/-- Equivalent explicit form of `relation_of_imbalance`: a non-balancing verifying bundle yields the
discrete log of `V` base `R`, namely `dlog_R V = A⁻¹ (bsk − B)`. This is the constructive extraction
the AGM / DLR wrappers feed to discrete-log hardness. -/
theorem rand_log_of_imbalance (V R bvk : M) (A B bsk : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    V = (A⁻¹ * (bsk - B)) • R := by
  have hVR := smul_value_eq_smul_rand V R bvk A B bsk hExtract hSum
  have h : A⁻¹ • (A • V) = A⁻¹ • ((bsk - B) • R) := by rw [hVR]
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hA, one_smul] at h

/-! ### Abstract model (sanity check over a general module; NOT the group assumption)

The information-theoretic binding predicate below is satisfiable only when `V` and `R` are genuinely
independent — e.g. in a free `F`-module of rank ≥ 2. It validates the algebra of the reduction but
is **false** in a prime-order group and is never instantiated there; the group uses
`relation_of_imbalance` + DLR-hardness instead. -/

/-- Information-theoretic binding: the only `F`-linear relation between `V` and `R` is trivial.
Satisfiable only in rank-≥2 models; false in a cyclic group. -/
def Binding (V R : M) : Prop := ∀ a b : F, a • V + b • R = 0 → a = 0 ∧ b = 0

/-- In an abstract model where `Binding` holds, a verifying bundle balances in `F`. -/
theorem balances_of_binding (V R : M) (A B bsk : F)
    (hbind : Binding (F := F) V R)
    (hVR : A • V = (bsk - B) • R) :
    A = 0 := by
  have h0 : A • V + (B - bsk) • R = 0 := by
    rw [hVR, ← add_smul]
    have hc : (bsk - B) + (B - bsk) = (0 : F) := by ring
    rw [hc, zero_smul]
  exact (hbind A (B - bsk) h0).1

/-- Abstract-model combination: extractability + decomposition + (idealized) binding ⟹ `A = 0`. -/
theorem value_coeff_zero (V R bvk : M) (A B bsk : F)
    (hbind : Binding (F := F) V R)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A = 0 :=
  balances_of_binding V R A B bsk hbind
    (smul_value_eq_smul_rand V R bvk A B bsk hExtract hSum)

/-! ### Integer balance: range / no-overflow lift

`value_coeff_zero` (and the group-faithful reduction) conclude `A = 0` in `F = ZMod r` — balance
*modulo the scalar-field order*. Genuine balance is the integer equation
`∑ v_in − ∑ v_out − v_balance = 0`. The two coincide because note values and `v_balance` are bounded,
so the integer balance cannot wrap mod `r`: with note values in `[0, MAX_MONEY]` and at most
`maxActions` of them, the integer balance `N` has `N.natAbs < r` whenever `MAX_MONEY · maxActions < r`
— comfortably true for Pasta (`r ≈ 2^254`, `MAX_MONEY ≈ 2^51`). The lift is then pure arithmetic. -/

/-- No-overflow lift: an integer reducing to `0` mod `r` whose magnitude is `< r` is `0`. This turns
balance modulo the scalar-field order (`A = 0` in `ZMod r`) into integer balance, given the value
sums cannot wrap. -/
theorem intBalance_eq_zero_of_lt {r : ℕ} [NeZero r] (N : ℤ)
    (hmod : (N : ZMod r) = 0) (hlt : N.natAbs < r) : N = 0 := by
  obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd N r).mp hmod
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    have habs : ((r : ℤ) * k).natAbs = r * k.natAbs := by simp [Int.natAbs_mul]
    rw [habs] at hlt
    have hle : r ≤ r * k.natAbs := by
      calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * k.natAbs := Nat.mul_le_mul (le_refl r) hpos
    omega

/-- The same lift phrased with an integer absolute-value bound `|N| < r`. -/
theorem intBalance_eq_zero_of_abs_lt {r : ℕ} [NeZero r] (N : ℤ)
    (hmod : (N : ZMod r) = 0) (hlt : |N| < (r : ℤ)) : N = 0 := by
  apply intBalance_eq_zero_of_lt N hmod
  rwa [Int.abs_eq_natAbs, Nat.cast_lt] at hlt

/-! ### Deriving the decomposition from a bundle (homomorphic value commitments)

The hypothesis `bvk = A • V + B • R` consumed above is not an assumption: it is *derived* from the
homomorphic value commitment `cv v rcv = v • V + rcv • R` and the shape of a bundle — lists of
spend / output `(value, randomness)` pairs together with the declared `vBalance`. -/

/-- The value commitment `cv v rcv = v • V + rcv • R`. -/
def valueCommit (V R : M) (v rcv : F) : M := v • V + rcv • R

/-- A sum of value commitments decomposes as the value-sum times `V` plus the randomness-sum times
`R` — the homomorphic property. -/
theorem sum_valueCommit (V R : M) (l : List (F × F)) :
    (l.map fun p => valueCommit V R p.1 p.2).sum
      = (l.map Prod.fst).sum • V + (l.map Prod.snd).sum • R := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [valueCommit, add_smul]
    abel

/-- The binding verification key of a bundle: sum of spend commitments minus sum of output
commitments minus `vBalance • V`. -/
def bindingVK (V R : M) (spends outputs : List (F × F)) (vBalance : F) : M :=
  (spends.map fun p => valueCommit V R p.1 p.2).sum
    - (outputs.map fun p => valueCommit V R p.1 p.2).sum - vBalance • V

/-- **`hSum`, derived.** The binding verification key decomposes homomorphically as `A • V + B • R`,
with `A` the net value (`∑ spend values − ∑ output values − vBalance`) and `B` the net randomness
(`∑ spend randomness − ∑ output randomness`). -/
theorem bindingVK_decomp (V R : M) (spends outputs : List (F × F)) (vBalance : F) :
    bindingVK V R spends outputs vBalance
      = ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance) • V
        + ((spends.map Prod.snd).sum - (outputs.map Prod.snd).sum) • R := by
  rw [bindingVK, sum_valueCommit, sum_valueCommit]
  simp only [sub_smul]
  abel

/-- Putting it together: for a bundle whose binding signature verifies (RedDSA extractability gives
`bvk = bsk • R`) and under (idealized) binding, the net value coefficient is zero **in `F`** — i.e.
balance *modulo the scalar-field order*, with no `hSum` assumption (the decomposition is derived by
`bindingVK_decomp`). This is **not** integer balance: lifting it to `∑ v_in = ∑ v_out + v_balance`
over ℤ needs the range / no-overflow step `intBalance_eq_zero_of_lt`, which is not applied here. -/
theorem bundle_mod_balances (V R : M) (spends outputs : List (F × F)) (vBalance bsk : F)
    (hbind : Binding (F := F) V R)
    (hExtract : bindingVK V R spends outputs vBalance = bsk • R) :
    (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = 0 :=
  value_coeff_zero V R (bindingVK V R spends outputs vBalance) _ _ bsk hbind hExtract
    (bindingVK_decomp V R spends outputs vBalance)

/-- **Integer value balance** — the second stage of the spec §4.13 / §4.14 argument. Stage 1
(`bundle_mod_balances`) gives `A = 0` in `ZMod r`, i.e. balance *modulo the scalar-field order*. When
that `A` is the reduction of an integer net value `N` that cannot wrap (`|N| < r`, guaranteed by
`MAX_MONEY · maxActions < r`), the range / no-overflow lift `intBalance_eq_zero_of_lt` upgrades it to
`N = 0` over ℤ — genuine integer value balance. -/
theorem bundle_integer_balances {r : ℕ} [Fact (Nat.Prime r)]
    {M : Type*} [AddCommGroup M] [Module (ZMod r) M]
    (V R : M) (spends outputs : List (ZMod r × ZMod r)) (vBalance bsk : ZMod r) (N : ℤ)
    (hcast : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = (N : ZMod r))
    (hbound : N.natAbs < r)
    (hbind : Binding (F := ZMod r) V R)
    (hExtract : bindingVK V R spends outputs vBalance = bsk • R) :
    N = 0 := by
  haveI : NeZero r := ⟨(Fact.out : Nat.Prime r).pos.ne'⟩
  refine intBalance_eq_zero_of_lt N ?_ hbound
  rw [← hcast]
  exact bundle_mod_balances V R spends outputs vBalance bsk hbind hExtract

end Zcash.Security.BindingSignature
