import Mathlib.Algebra.Group.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Tactic
import Zcash.Tactic

-- Complete Twisted Edwards elliptic curves as defined in Hüseyin Hışıl's thesis:
-- Elliptic Curves, Group Law, and Efficient Computation
-- <https://eprints.qut.edu.au/33233/1/H%C3%BCseyin_Hi%C5%9Fil_Thesis.pdf>

variable (F : Type) [field_F : Field F]

structure CtEdwardsCurve where
  a : F
  d : F
  a_d_distinct : a ≠ d
  a_nonzero : a ≠ 0
  sqrt_a : F
  a_square : sqrt_a^2 = a
  d_nonsquare : ¬IsSquare d
  F_nonbinary : (2 : F) ≠ 0
deriving Repr

def ctedwards_on_curve (a d u v : F) : Prop :=
  a * u^2 + v^2 = 1 + d * u^2 * v^2

lemma ctedwards_d_nonzero (E : CtEdwardsCurve F) : E.d ≠ 0 := by
  let d_nonsq := E.d_nonsquare
  by_contra d_contra
  rw [d_contra] at d_nonsq
  simp_all only [IsSquare.zero, not_true_eq_false]

lemma only_nz_squared_is_nz (a : F) (a_sq_nz : a^2 ≠ 0) : a ≠ 0 := by
  rw [sq, mul_ne_zero_iff] at a_sq_nz
  simp_all only [ne_eq, not_false_eq_true]

lemma ctedwards_sqrt_a_nz (E : CtEdwardsCurve F) : E.sqrt_a ≠ 0 := by
  let a_nz := E.a_nonzero
  rw [← E.a_square] at a_nz
  exactly only_nz_squared_is_nz at a_nz


structure CtEdwardsPoint (E : CtEdwardsCurve F) where
  u : F
  v : F
  on_curve : ctedwards_on_curve F E.a E.d u v
deriving Repr

lemma div_pow_comm (a b : F) : (a / b)^2 = a^2 / b^2 := by field_simp

lemma mul_pow_comm_conv (a b : F) : a^2 * b^2 = (a * b)^2 := by ring_nf

lemma nz_squared_is_nz (a : F) (a_nz : a ≠ 0) : a^2 ≠ 0 := by field_simp

lemma only_zero_squared_is_zero (a : F) (a_sq_zero : a^2 = 0) : a = 0 := by
  rw [sq] at a_sq_zero
  by_contra contra
  have both : a ≠ 0 ∧ a ≠ 0 := by simp_all only [mul_eq_zero, or_self]
  apply Iff.mpr mul_ne_zero_iff at both
  contradiction

lemma div_nz (a b d : F) (mult : a = d * b) : b = 0 ∨ d = a / b := by
  by_cases b_nz : b ≠ 0
  . have goal : d = a / b := by
      apply eq_div_of_mul_eq
      . exact b_nz
      . exact Eq.symm mult
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel, or_true]
  . simp_all only [not_not, true_or]

lemma detect_square (w d : F) (square : d = w^2) : IsSquare d := by
  rw [IsSquare]
  rw [sq] at square
  subst square
  apply Exists.intro
  . rfl

lemma add_field_eqns (a b c d : F) (fst : a = b) (snd : c = d) : a + c = b + d := by
  have h : a + c = b + c := by exact congrFun (congrArg HAdd.hAdd fst) c
  rw [← snd]
  exact h

--set_option maxHeartbeats 500000
--tactics to avoid:
--  tauto
--  simp_all without 'only [...]'

lemma ctedwards_complete (E : CtEdwardsCurve F) (P₁ P₂ : CtEdwardsPoint F E)
    : (E.d*(P₂.u*(P₂.v*(P₁.u*P₁.v))))^2 ≠ 1 := by
  let u₁ := P₁.u; let v₁ := P₁.v; let u₂ := P₂.u; let v₂ := P₂.v
  let ε := E.d*(u₂*(v₂*(u₁*v₁)))
  let curve₁ : ctedwards_on_curve F E.a E.d u₁ v₁ := P₁.on_curve
  let curve₂ : ctedwards_on_curve F E.a E.d u₂ v₂ := P₂.on_curve

  /-
  Adaptation of Theorem 3.3 in <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>

  Convention: ± refers to a single sign in any given formula.

  Suppose ε^2 = 1. Then u₁, u₂, v₁, v₂ ≠ 0. Furthermore
    d*u₁^2*v₁^2*(a*u₂^2 + v₂^2) = d*u₁^2*v₁^2*(1 + d*u₂^2*v₂^2)          [curve eq₂]
                                = d*u₁^2*v₁^2 + d^2*u₁^2*v₁^2*u₂^2*v₂^2
                                = d*u₁^2*v₁^2 + ε^2                      [defn ε]
                                = 1 + d*u₁^2*v₁^2                        [ε ∈ {-1, 1}]
                                = a*u₁^2 + v₁^2                          [curve eq₁] (h1)
  so
    ((√a)*u₁ + ε*v₁)^2 = a*u₁^2 + v₁^2 ± 2*(√a)*ε*u₁*v₁                  (h2) ---------------.
                       = d*u₁^2*v₁^2*(a*u₂^2 + v₂^2) ± 2*(√a)*ε*u₁*v₁    [subst h1]          | (h3)
                       = d*u₁^2*v₁^2*(a*u₂^2 + v₂^2 ± 2*(√a)*u₂*v₂)      [expand, defn ε]    v
                       = d*u₁^2*v₁^2*((√a)*u₂ ± v₂)^2                    [rewrite square]  (h4)

  If (√a)*u₂ ± v₂ ≠ 0 then d = ((√a)*u₁ ± ε*v₁)/(u₁*v₁*((√a)*u₂ ± v₂))^2 so d is a square, contradiction.
  If both (√a)*u₂ + v₂ and (√a)*u₂ - v₂ are 0 then u₂ = 0 and v₂ = 0, contradiction.
  -/

  have ε_sq_n1 : ε^2 ≠ 1 := by
    by_contra ε_sq_1
    have ε_sq_nz  : ε^2 ≠ 0 := by simp_all only [zero_ne_one]; field_simp
    have ε_nz     : ε ≠ 0 := by exactly only_nz_squared_is_nz at ε_sq_nz
    repeat (rw [mul_ne_zero_iff] at ε_nz)
    have h1       : E.d*((u₁*v₁)^2*(E.a*u₂^2 + v₂^2)) = E.a*u₁^2 + v₁^2 := by
      rw [curve₁, ← ε_sq_1]; unfold ε; rw [curve₂]; ring

    have signed_arg (sign : F) (sign_sq_1 : sign^2 = 1) : E.sqrt_a*u₂ + sign*v₂ = 0 := by
      -- ε changes sign with v₂
      let pm_v₂ := sign*v₂; let pm_ε := sign*ε

      have h2       : (E.sqrt_a*u₁ + pm_ε*v₁)^2 = E.a*u₁^2 + v₁^2 + 2*E.sqrt_a*pm_ε*(u₁*v₁) := by
        unfold pm_ε; ring_nf
        rw [ε_sq_1, sign_sq_1, E.a_square]; ring
      have h3       : E.a*u₁^2 + v₁^2 + 2*E.sqrt_a*pm_ε*(u₁*v₁) = E.d*((u₁*v₁)^2*(E.sqrt_a*u₂ + pm_v₂)^2) := by
        rw [← h1]
        unfold pm_ε; unfold ε; unfold pm_v₂; ring_nf
        rw [sign_sq_1, E.a_square]; ring
      have h4       : (E.sqrt_a*u₁ + pm_ε*v₁)^2 = E.d*((u₁*v₁)^2*(E.sqrt_a*u₂ + pm_v₂)^2) := by
        rw [h2, h3]
      have d_calc   : ((u₁*v₁)*(E.sqrt_a*u₂ + pm_v₂))^2 = 0 ∨
                        E.d = (E.sqrt_a*u₁ + pm_ε*v₁)^2 / ((u₁*v₁)*(E.sqrt_a*u₂ + pm_v₂))^2 := by
        rw [mul_pow_comm_conv] at h4
        exactly div_nz at h4
      have d_contra : E.d ≠ (E.sqrt_a*u₁ + pm_ε*v₁)^2 / ((u₁*v₁)*(E.sqrt_a*u₂ + pm_v₂))^2 := by
        by_contra d_square
        have d_sq     : E.d = ((E.sqrt_a*u₁ + pm_ε*v₁) / ((u₁*v₁)*(E.sqrt_a*u₂ + pm_v₂)))^2 := by
          rw [← div_pow_comm] at d_square; exact d_square
        apply E.d_nonsquare
        exactly detect_square at d_sq
      simp_all only [d_calc]; simp at d_calc
      simp_all only [false_or, pm_v₂]

    have sign_p1  : (1 : F)^2 = 1 := by ring
    have plus_v₂  : E.sqrt_a*u₂ + (1 : F)*v₂ = 0 := by apply signed_arg (1 : F) sign_p1
    simp at plus_v₂

    have sign_m1  : (-1 : F)^2 = 1 := by ring
    have minus_v₂ : E.sqrt_a*u₂ + (-1 : F)*v₂ = 0 := by apply signed_arg (-1 : F) sign_m1
    simp at minus_v₂

    have sqrta_u₂_2_z : E.sqrt_a*(u₂*2) = 0 := by
      have added    : (E.sqrt_a*u₂ + v₂) + (E.sqrt_a*u₂ + -v₂) = 0 + 0 := by
        apply add_field_eqns
        . exact plus_v₂
        . exact minus_v₂
      ring_nf at added; ring_nf; exact added
    have sqrta_or_u₂_2_z : E.sqrt_a = 0 ∨ u₂*2 = 0 := by simp_all only [Iff.mp mul_eq_zero, false_or]
    have sqrta_nz : E.sqrt_a ≠ 0 := by apply ctedwards_sqrt_a_nz
    have u₂_2_z   : u₂*2 = 0 := by simp_all only [false_or]
    let  two_nz   := E.F_nonbinary
    have u₂_z     : u₂ = 0 := by apply Iff.mp mul_eq_zero at u₂_2_z; simp_all only [two_nz]; simp at u₂_2_z
    -- similarly we also have v₂ = 0, but we don't need that
    simp_all only [u₂]

  unfold ε at ε_sq_n1; exact ε_sq_n1


def ctedwards_add (E : CtEdwardsCurve F) (P₁ P₂ : CtEdwardsPoint F E) : CtEdwardsPoint F E :=
  let u₁ := P₁.u; let v₁ := P₁.v; let u₂ := P₂.u; let v₂ := P₂.v
  let ε  := E.d*(u₂*(v₂*(u₁*v₁)))
  let u₃ := (u₁*v₂ + v₁*u₂) / (1 + ε)
  let v₃ := (v₁*v₂ - E.a*u₁*u₂) / (1 - ε)

  { u := u₃, v := v₃,
    on_curve := by
      have ε_sq_n1  : ε^2 ≠ 1 := by apply ctedwards_complete F E P₁ P₂
      have ε_neq    : ε ≠ -1 ∧ ε ≠ 1 := by simp_all only [ne_eq, sq_eq_one_iff, not_or, not_false_eq_true, and_self]
      have u_den_nz : 1 + ε ≠ 0 := by
        by_contra u_den_contra; apply eq_zero_sub_of_add_eq_zero_right at u_den_contra; simp_all only [zero_sub, ε]
      have v_den_nz : 1 - ε ≠ 0 := by
        by_contra v_den_contra; apply eq_of_sub_eq_zero at v_den_contra; simp_all only [ne_eq, not_true_eq_false]

      let curve₁ : ctedwards_on_curve F E.a E.d u₁ v₁ := P₁.on_curve
      let curve₂ : ctedwards_on_curve F E.a E.d u₂ v₂ := P₂.on_curve
      sorry
  }

instance (E : CtEdwardsCurve F) : Add (CtEdwardsPoint F E) where
  add P₁ P₂ := ctedwards_add F E P₁ P₂

theorem ctedwards_add_commutative (E : CtEdwardsCurve F) (P₁ P₂ : CtEdwardsPoint F E) :
    ctedwards_add F E P₁ P₂ = ctedwards_add F E P₂ P₁ := by
  rw [ctedwards_add, ctedwards_add]
  ac_nf

theorem ctedwards_add_op_commutative (E : CtEdwardsCurve F) (P₁ P₂ : CtEdwardsPoint F E) :
    P₁ + P₂ = P₂ + P₁ := by
  apply ctedwards_add_commutative


-- Montgomery curves

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
