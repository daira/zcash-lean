import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Zcash.Tactic

import Zcash.Math.Groups

/-
Theorem A.3.4. Distinct-x theorem.

https://zips.z.cash/protocol/protocol.pdf#thmdistinctx

Let Q be a point of odd-prime order s on a Montgomery curve M = E_{Mont(A_M, B_M)} over 𝔽_{r_𝕊}.
Let k₁, k₂ be integers in {-(s-1)/2 .. (s-1)/2} \ {0}. Let Pᵢ = [ kᵢ ] Q = (xᵢ, yᵢ) for i ∈ {1,2},
with k₂ ≠ ±k₁. Then the non-unified addition constraints

  (x₂ - x₁) × (λ) = (y₂ - y₁)
  (B_M * λ) × (λ) = (A_M + x₁ + x₂ + x₃)
  (x₁ - x₃) × (λ) = (y₃ + y₁)

implement the affine-Montgomery addition P₁ + P₂ = (x₃, y₃) for all such P₁, P₂.

Proof. The given constraints are equivalent to the Montgomery addition formulae under the side
condition that x₁ ≠ x₂. (Note that neither Pᵢ can be the zero point since k₁, k₂ ≠ 0 (mod s).
Assume for a contradiction that x₁ = x₂. For any P₁ = [ k₁ ] Q, there can be only one other point
-P₁ with the same x-coordinate. (This follows from the fact that the curve equation determines ±y
as a function of x.) But -P₁ = -(k₁ • Q) = -k₁ • Q. Since k : {-(s-1)/2 .. (s-1)/2} ↦ k • Q : M
is injective and k₁, k₂ are in {-(s-1)/2 .. (s-1)/2}, then k₂ = ±k₁ (contradiction).
-/

/- Field of definition. We do not depend on it being a field. -/
variable (F : Type)

/- M is an additive group. -/
variable (M : Type) [AddGroup M]

/- The order of M is odd. -/
variable (s : ℕ)
variable (n : ℕ) (s_odd : s = 2*n + 1)
variable (smulwithzero : SMulWithZero (ZMod s) M)

/-- We define the range of non-zero scalars to be symmetric on 0, rather than unsigned. -/
def nz_symmetric_range : Set ℤ := { k | |k| ≤ n ∧ k ≠ 0 }

/-- If k ∈ nz_symmetric_range n then so is -k. -/
lemma neg_bij_on_nz_symmetric_range (k : ℤ) (kin : k ∈ nz_symmetric_range n) : -k ∈ nz_symmetric_range n := by
  unfold nz_symmetric_range at kin
  unfold nz_symmetric_range
  simp_all only [ne_eq, Set.mem_setOf_eq, abs_neg, neg_eq_zero, not_false_eq_true, and_self]

/-- Negating a non-zero point gives a non-zero point. -/
lemma negnz (P : nonzero M) : -(P:M) ∈ nonzero M := by
  obtain ⟨P, P_nz⟩ := P; simp_all only
  have mP_nz : -P ≠ 0 := by
    by_contra contra
    apply P_nz
    have mmP_eq_mz : -(-P) = -0 := by simp_all only
    have P_eq_mz : P = -0 := by group at mmP_eq_mz; exact mmP_eq_mz
    simp_all only [neg_zero]
  exact mP_nz

/-
TODO this states something that relies on an x-axis symmetry property that is true for
Montgomery and short Weierstrass curves, but does not prove that property for those curves.
-/

theorem distinct_x_axis_symmetric
    /-
    There is a projection of non-zero points of M to the x line on F.
    This is where we break open the group abstraction and consider M to have structure, such as an elliptic curve.
    -/
    (proj_x : nonzero M → F)
    -- Any two points of M that have the same projection to the x line are equal up to sign.
    (x_axis_symmetry : (R₁ : nonzero M) → (R₂ : nonzero M) → (proj_x R₁ = proj_x R₂) → ((R₁:M) = R₂ ∨ -(R₁:M) = R₂))
    -- Q is a point of M that we use as a generator.
    (Q : M)
    -- k : nz_symmetric_range n ↦ k • Q : M is injective. This requires Q to be of order at least s.
    (nz_symmetric_range_inj : Set.InjOn (fun (k : ℤ) => k • Q) (nz_symmetric_range n))
    -- k₁ and k₂ are non-zero scalars that span the order of M.
    (k₁ : nz_symmetric_range n)
    (k₂ : nz_symmetric_range n)
    -- k₁ and k₂ are not equal up to sign.
    (k₁_neq_k₂ : (k₁:ℤ) ≠ k₂) (mk₁_neq_k₂ : -(k₁:ℤ) ≠ k₂)
    -- P₁ = k₁ • Q and P₂ = k₂ • Q are non-zero points of M.
    (P₁ : nonzero M) (P₁_mul : P₁ = (k₁:ℤ) • Q)
    (P₂ : nonzero M) (P₂_mul : P₂ = (k₂:ℤ) • Q)
  : -- Then we conclude that P₁ and P₂ have distinct projections to the x line.
    proj_x P₁ ≠ proj_x P₂ :=
  by
    have hk₁ : ↑k₁ ∈ nz_symmetric_range n := by simp_all only [Subtype.coe_prop]
    have hk₂ : ↑k₂ ∈ nz_symmetric_range n := by simp_all only [Subtype.coe_prop]
    by_contra contra
    have h1 : (P₁:M) = P₂ ∨ -(P₁:M) = P₂ := by apply x_axis_symmetry; trivial
    have h2 : (k₁:ℤ) • Q = (k₂:ℤ) • Q ∨ (-(k₁:ℤ)) • Q = (k₂:ℤ) • Q := by simp_all only [neg_zsmul]
    cases h2 with
    | inl left => let k₁_eq_k₂ := nz_symmetric_range_inj hk₁ hk₂ left; contradiction
    | inr right => let mk₁_eq_k₂ := nz_symmetric_range_inj (neg_bij_on_nz_symmetric_range n k₁ hk₁) hk₂ right; contradiction
