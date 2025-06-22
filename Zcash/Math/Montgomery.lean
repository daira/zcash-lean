import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.Tactic
import Zcash.Tactic

import Zcash.Math.Groups
import Zcash.Math.CtEdwards

/-
Montgomery curves. TODO: references.
-/

variable (F : Type) [field_F : Field F]

/--
We don't want the lack of `[Repr (WeierstrassCurve F)]` to prevent deriving
`Repr` for `MontgomeryCurve`.
-/
local instance {F : Type} : Repr (WeierstrassCurve F) where
  reprPrec _ _ := "WeierstrassCurve"

/-- A Montgomery elliptic curve over a non-binary field. -/
structure MontgomeryCurve where
  A : F
  B : F
  W : WeierstrassCurve.Affine F
  B_is_1 : B = 1
  nonsingular : 16*A^2 - 64 ≠ 0
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = A
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 1
  a₆ : W.a₆ = 0
  F_nonbinary : (2:F) ≠ 0
deriving Repr

variable (M : MontgomeryCurve F)

/--
This implies via `WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero` that
M is nonsingular at every affine point on the curve.
-/
lemma mont_Δ_nz : M.W.Δ ≠ 0 := by
  let W := M.W
  unfold WeierstrassCurve.Δ
  simp_all only [neg_mul, W]
  unfold WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆ WeierstrassCurve.b₈
  rw [M.a₁, M.a₂, M.a₃, M.a₄, M.a₆]
  let nonsingular := M.nonsingular
  ring_nf; ring_nf at nonsingular
  exact nonsingular

/--
All pairs (x, y) satisfying the curve equation correspond to a nonsingular point of M,
and conversely.
-/
theorem montgomery_affine_eqn (M : MontgomeryCurve F) {x y : F} : M.W.Equation x y ↔ M.W.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (mont_Δ_nz F M)

/-- Δ is a unit. -/
lemma mont_Δ_is_unit : IsUnit M.W.Δ := by
  unfold IsUnit
  apply Units.exists0.mpr
  use M.W.Δ
  use mont_Δ_nz F M
  simp only [Units.val_mk0]

/-- Montgomery curves are elliptic. -/
instance mont_is_elliptic : M.W.IsElliptic :=
  ⟨mont_Δ_is_unit F M⟩

/--
A `MontgomeryPoint` uses the Mathlib implementation of `WeierstrassCurve.Affine.Point`.
This must be a `def`, not an `abbrev`, because the Mathlib typeclass instances are
noncomputable.
-/
def MontgomeryPoint := M.W.toAffine.Point

/-
The implementations of `proj_x` and `proj_y` violate an abstraction boundary between
this code and Mathlib, and should be moved into the latter. To be clear, the problem
isn't that we expose the coordinates, it's that this approach depends quite heavily
on the implementation of `WeierstrassCurve.Affine.Point` in Mathlib.
-/

/-- The x-coordinate of a `MontgomeryPoint`, if it exists. -/
def proj_x (P : MontgomeryPoint F M) : Option F :=
  match P with
    | @WeierstrassCurve.Affine.Point.some F _ M.W x _y (_h : M.W.Nonsingular x _y) => some x
    | .zero => none

/-- The y-coordinate of a `MontgomeryPoint`, if it exists. -/
def proj_y (P : MontgomeryPoint F M) : Option F :=
  match P with
    | @WeierstrassCurve.Affine.Point.some F _ M.W _x y (_h : M.W.Nonsingular _x y) => some y
    | .zero => none

instance mont_zero : Zero (MontgomeryPoint F M) where
  zero := .zero

@[simp]
lemma mont_zero_def : 0 = (.zero : MontgomeryPoint F M) := rfl

instance mont_neg : Neg (MontgomeryPoint F M) where
  neg (P : MontgomeryPoint F M) : MontgomeryPoint F M := P.neg

lemma neg_def (P : MontgomeryPoint F M) : -P = P.neg := rfl

@[simp]
lemma mont_neg_zero : (-.zero : MontgomeryPoint F M) = .zero := rfl

/-- Negation for nonsingular points. -/
lemma mont_neg_some {x y : F} (h : M.W.Nonsingular x y)
    : -WeierstrassCurve.Affine.Point.some h = .some ((WeierstrassCurve.Affine.nonsingular_neg x y).mpr h) := rfl

/-- Nonsingular case of the negation formula. -/
lemma mont_nonsingular_neg_some {x₁ y₁ x₂ y₂ : F} (h₁ : M.W.Nonsingular x₁ y₁) (h₂ : M.W.Nonsingular x₂ y₂)
    (hneg : WeierstrassCurve.Affine.Point.some h₁ = -WeierstrassCurve.Affine.Point.some h₂)
    : x₁ = x₂ ∧ y₁ = -y₂ - M.W.a₁ * x₂ - M.W.a₃ := by simp_all

/-
Everything here is working around a design problem (from our perspective) with
`WeierstrassCurve.Affine` in Mathlib: even when we have `[DecidableEq F]`, some
internals, in particular `WeierstrassCurve.Affine.slope`, are marked as noncomputable
so we cannot use it constructively without some circumlocution.

This approach would actually work for all Weierstrass *elliptic* curves with
`[DecidableEq F]`, not just Montgomery curves. The tricky part of moving it into
Mathlib would be to avoid breaking stuff that doesn't require `[DecidableEq F]`.
-/

variable [DecidableEq F]

/--
Copied from Mathlib's `WeierstrassCurve.Affine.slope` to make it computable.
The proofs in this file depend on using the same definition as Mathlib at least
up to `simp_all` equivalence.
-/
def compute_slope (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then if y₁ = M.W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * M.W.a₂ * x₁ + M.W.a₄ - M.W.a₁ * y₁) / (y₁ - M.W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

/-- Computability aside, `compute_slope` is consistent with `WeierstrassCurve.Affine.slope`. -/
lemma mont_slope_matches (x₁ x₂ y₁ y₂ : F)
    : M.W.slope x₁ x₂ y₁ y₂ = compute_slope F M x₁ x₂ y₁ y₂ := by
  simp_all only [WeierstrassCurve.Affine.slope, compute_slope]

/--
Computable addition of two nonsingular points. Note that this takes `Nonsingular`
hypotheses as input, but returns a `MontgomeryPoint`.
-/
def mont_add_some (x₁ y₁ x₂ y₂ : F) (h₁ : M.W.Nonsingular x₁ y₁) (h₂ : M.W.Nonsingular x₂ y₂)
    : MontgomeryPoint F M :=
  let ℓ : F := compute_slope F M x₁ x₂ y₁ y₂
  let x₃ : F := M.W.addX x₁ x₂ ℓ
  let y₃ : F := M.W.addY x₁ x₂ y₁ ℓ
  if hxy : x₁ = x₂ ∧ y₁ = M.W.negY x₂ y₂ then 0 else
    let h := M.W.nonsingular_add h₁ h₂ hxy
    .some (by rw [mont_slope_matches] at h; trivial)

/-- The implementation of addition for `MontgomeryPoint`. -/
def mont_add (P₁ P₂ : MontgomeryPoint F M) : MontgomeryPoint F M :=
  match P₁, P₂ with
    | 0, P => P
    | P, 0 => P
    | @WeierstrassCurve.Affine.Point.some F _ M.W x₁ y₁ (h₁ : M.W.Nonsingular x₁ y₁),
      @WeierstrassCurve.Affine.Point.some F _ M.W x₂ y₂ (h₂ : M.W.Nonsingular x₂ y₂) =>
        mont_add_some F M x₁ y₁ x₂ y₂ h₁ h₂

/-- Computability aside, `mont_add` is consistent with `WeierstrassCurve.Affine.Point.instAddCommGroup.add`. -/
lemma mont_add_matches {x₁ y₁ x₂ y₂ : F} (h₁ : M.W.Nonsingular x₁ y₁) (h₂ : M.W.Nonsingular x₂ y₂)
    : (WeierstrassCurve.Affine.Point.some h₁) + (WeierstrassCurve.Affine.Point.some h₂) = mont_add F M (.some h₁) (.some h₂) := by
  unfold HAdd.hAdd instHAdd
  simp_all only [Add.add, WeierstrassCurve.Affine.Point.instAdd, WeierstrassCurve.Affine.Point.add,
                 WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
                 WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
                 neg_add_rev, mont_add, mont_add_some, compute_slope]

/-- `mont_add_some` is commutative. -/
lemma mont_add_some_comm (x₁ y₁ x₂ y₂ : F) (h₁ : M.W.Nonsingular x₁ y₁) (h₂ : M.W.Nonsingular x₂ y₂)
    : mont_add_some F M x₁ y₁ x₂ y₂ h₁ h₂ = mont_add_some F M x₂ y₂ x₁ y₁ h₂ h₁ := by
  let hw := WeierstrassCurve.Affine.Point.instAddCommGroup.add_comm (.some h₁) (.some h₂)
  rw [mont_add_matches] at hw
  simp_all only [Add.add, WeierstrassCurve.Affine.Point.instAdd, WeierstrassCurve.Affine.Point.add,
                 WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
                 WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
                 mont_add, mont_add_matches]

instance inst_mont_add : Add (MontgomeryPoint F M) :=
  ⟨mont_add F M⟩

instance inst_mont_addzero : AddZeroClass (MontgomeryPoint F M) :=
  ⟨by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩

lemma add_def (P Q : MontgomeryPoint F M) : P + Q = mont_add F M P Q :=
  rfl

local syntax "unfold_add" : tactic
macro_rules
| `(tactic| unfold_add ) =>
  `(tactic| unfold HAdd.hAdd instHAdd; simp only; unfold Add.add inst_mont_add mont_add; simp only )

/-- a + b = 0 → a = -b. -/
lemma mont_zero_sum_imp_neg (a b : MontgomeryPoint F M) : (hz : mont_add F M a b = 0) → a = -b := by
  unfold mont_add
  split <;> try rw [mont_zero_def]; simp_all
  rename_i xa ya ha xb yb hb
  unfold mont_add_some mont_neg WeierstrassCurve.Affine.Point.neg
  simp_all

instance mont_group (M : MontgomeryCurve F) : AddCommGroup (MontgomeryPoint F M) where
  zsmul := zsmulRec
  nsmul := nsmulRec
  zero_add := by simp
  add_zero := by simp
  neg_add_cancel := by
    intro P -- -P + P = 0
    unfold_add
    split
    . -- (-P, P) = (0, P)
      rename_i h
      unfold Neg.neg mont_neg at h; simp only at h; unfold WeierstrassCurve.Affine.Point.neg at h
      split at h <;> trivial
    . rfl
    . rename_i x₁ y₁ h₁ x₂ y₂ h₂ hneg -- -P₂ = P₁ nonsingular negation formula
      unfold mont_add_some
      simp
      exact mont_nonsingular_neg_some F M h₁ h₂ hneg.symm
  add_comm := by
    intro a b
    unfold_add
    split <;> try split <;> trivial -- this disposes of easy cases
    rename_i xa ya ha xb yb hb
    exact mont_add_some_comm F M xa ya xb yb ha hb
  add_assoc := by
    intro a b c -- a + b + c = a + (b + c)
    unfold_add
    split <;> (try split <;> simp_all)
    . sorry
    . sorry

/-- Any two points of M that have the same projection to the x line are equal up to sign. -/
theorem montgomery_x_axis_symmetry
    (P₁ : MontgomeryPoint F M) (P₂ : MontgomeryPoint F M) (x_eq : proj_x F M P₁ = proj_x F M P₂)
    : P₁ = P₂ ∨ -P₁ = P₂ := by
  sorry


/-
def edwards_to_montgomery_point (E : CtEdwardsCurve F) (M : MontgomeryCurve F) (P : CtEdwardsPoint F E)
    : MontgomeryPoint F M :=
  MontgomeryPoint.some {
    x := (1 + P.v) / (1 - P.v),
    y := (1 + P.v) / ((1 - P.v) * P.u),
    h := sorry,
    on_curve := sorry,
  }

--def edwards_to_montgomery_curve (E : CtEdwardsCurve F) : WeierstrassCurve F := ...
-/
