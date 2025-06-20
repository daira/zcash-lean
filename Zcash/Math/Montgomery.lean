import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Tactic
import Zcash.Tactic

import Zcash.Math.CtEdwards

-- Montgomery curves

variable (F : Type) [field_F : Field F]

local instance {F : Type} : Repr (WeierstrassCurve F) where
  reprPrec _ _ := "WeierstrassCurve"

structure MontgomeryCurve where
  A : F
  B : F
  W : WeierstrassCurve.Affine F
  W_elliptic : WeierstrassCurve.IsElliptic W
  B_is_1 : B = 1
  W_a1 : W.a₁ = 0
  W_a2 : W.a₂ = A
  W_a3 : W.a₃ = 0
  W_a4 : W.a₄ = 1
  W_a6 : W.a₆ = 0
  F_nonbinary : (2 : F) ≠ 0
deriving Repr

structure MontgomeryAffinePoint (M : MontgomeryCurve F) where
  x : F
  y : F
  h : M.W.Nonsingular x y
  on_curve : M.B * y^2 = x^3 + M.A * x^2 + x
deriving Repr

inductive MontgomeryPoint (M : MontgomeryCurve F) where
  | zero : MontgomeryPoint M
  | some (P : MontgomeryAffinePoint F M) : MontgomeryPoint M

def edwards_to_montgomery_point (E : CtEdwardsCurve F) (M : MontgomeryCurve F) (P : CtEdwardsPoint F E)
    : MontgomeryPoint F M :=
  MontgomeryPoint.some {
    x := (1 + P.v) / (1 - P.v),
    y := (1 + P.v) / ((1 - P.v) * P.u),
    h := sorry,
    on_curve := sorry,
  }

def affine_montgomery_to_weierstrass_point (M : MontgomeryCurve F) (P : MontgomeryAffinePoint F M)
    : WeierstrassCurve.Affine.Point M.W :=
  WeierstrassCurve.Affine.Point.some P.h

def montgomery_to_weierstrass_point (M : MontgomeryCurve F) (P : MontgomeryPoint F M)
    : WeierstrassCurve.Affine.Point M.W :=
  match P with
  | .zero => WeierstrassCurve.Affine.Point.zero
  | .some P' => affine_montgomery_to_weierstrass_point F M P'

open Classical in

noncomputable instance (M : MontgomeryCurve F) : Add (MontgomeryPoint F M) where
  add
    | P, .zero => P
    | .zero, Q => Q
    | .some P, .some Q =>
      if P.x = Q.x ∧ P.y = -Q.y then
        .zero
      else
        let R := (affine_montgomery_to_weierstrass_point F M P) + (affine_montgomery_to_weierstrass_point F M Q)
        let ℓ := M.W.slope P.x Q.x P.y Q.y
        let x := M.W.addX P.x Q.x ℓ
        let y := M.W.addY P.x Q.x P.y ℓ
        match R with
          | .zero => MontgomeryPoint.zero
          | .some h => MontgomeryPoint.some { x := x, y := y, h := sorry, on_curve := sorry }

--def edwards_to_montgomery_curve (E : CtEdwardsCurve F) : WeierstrassCurve F := ...
