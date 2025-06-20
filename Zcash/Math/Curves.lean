import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Zcash.Tactic

/-
Theorem A.3.4. Distinct-x theorem.

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
as a function of x.) But -P₁ = [ -1 ] [ k₁ ] Q = [ -k₁ ] Q. Since k : {-(s-1)/2 .. (s-1)/2} ↦ [ k ] Q : M
is injective and k₁, k₂ are in {-(s-1)/2 .. (s-1)/2}, then k₂ = ±k₁ (contradiction).
-/

variable (F : Type) [Field F] -- field of definition
variable (s : ℕ) (prime_s : Prime s) (s_gt_2 : s > 2)

variable (M : Type) [AddGroup M] [Zero M]
variable (smulwithzero : SMulWithZero (ZMod s) M)

/-
TODO this states something that relies on an x-axis symmetry property that is true for
Montgomery and short Weierstrass curves, but does not prove that property for those curves.
-/

theorem distinct_x_axis_symmetric
    (k₁ : ℤ) (k₁_in_range : -(s-1)/2 ≤ k₁ ∧ k₁ ≤ (s-1)/2) (k₁_nz : k₁ ≠ 0)
    (k₂ : ℤ) (k₂_in_range : -(s-1)/2 ≤ k₂ ∧ k₂ ≤ (s-1)/2) (k₂_nz : k₂ ≠ 0)
    (pm_k₁_neq_k₂ : k₁ ≠ k₂ ∧ -k₁ ≠ k₂)
    (P₁ : M) (P₂ : M) (Q : M) (Q_nz : Q ≠ 0)
    (P₁_mul : P₁ = k₁ • Q)
    (P₂_mul : P₂ = k₂ • Q)
    (order_s : (k : ZMod s) → (k_nz : k ≠ 0) → (P : M) → (P_nz : P ≠ 0) → k • P ≠ 0)
    (proj_x : M → F)
    (x_axis_symmetry : (P₁ : M) → (P₂ : M) → (proj_x P₁ = proj_x P₂) → (P₁ = P₂ ∨ -P₁ = P₂))
  : proj_x P₁ ≠ proj_x P₂ := by
  by_contra
  have h1 : P₁ = P₂ ∨ -P₁ = P₂ := by apply x_axis_symmetry; trivial
  have h2 : k₁ • Q = k₂ • Q ∨ (-k₁) • Q = k₂ • Q := by simp_all only [neg_zsmul]
  sorry
