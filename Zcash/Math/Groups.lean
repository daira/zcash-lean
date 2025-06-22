import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

variable (G : Type) [AddGroup G]

/- The order of G. -/
variable (s : ℕ)
variable (smulwithzero : SMulWithZero (ZMod s) G)

/-- The set of nonzero elements in a group. -/
def nonzero : Set G := { P | P ≠ 0 }

/-
Doubling is injective on a group of odd order.

<https://math.stackexchange.com/questions/522273/if-a-group-g-has-odd-order-then-the-square-function-is-injective/522277#522277>
(translated to additive notation)

Suppose |G| = s = 2n + 1. Assume 2 • a = 2 • b.
Then a = a + (2n + 1) • a = (n+1) • 2 • a = (n+1) • 2 • b = b.
-/
theorem odd_order_double_inj
  (a b : G)
  (n : ℕ) (s_odd : s = 2*n + 1)
  /- The order of any element divides the order of the group. All we need is that the orders
     of `a` and of `b` divide `s` which is odd. -/
  (a_order_divides_s : s • a = 0) (b_order_divides_s : s • b = 0)
  (sq_eq : 2 • a = 2 • b)
: a = b :=
by
  have lem (x : G) (x_order_divides_s : s • x = 0) : (n+1) • 2 • x = x := by
    apply_fun fun y => x + y at x_order_divides_s
    rw [s_odd, add_zero, ← succ_nsmul'] at x_order_divides_s
    rw [← mul_nsmul]
    exact x_order_divides_s

  let ha := lem a a_order_divides_s
  let hb := lem b b_order_divides_s
  rw [sq_eq] at ha
  rw [ha] at hb
  exact hb
