import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

section
-- Doubling is injective on a group of odd order.
--
-- <https://math.stackexchange.com/questions/522273/if-a-group-g-has-odd-order-then-the-square-function-is-injective/522277#522277>
--
-- Let |G| = 2n - 1. Assume a^2 = b^2.
-- Then a = a * a^(2*n - 1) = (a^2)^n = (b^2)^n = b.

variable (G : Type) [Group G]

theorem expand_pow (a : G) (b c : Nat) : a^(b*c) = (a^b)^c := by
  group

theorem odd_order_double_inj (n : Nat) (a b : G) : a^(2*n) = a -> b^(2*n) = b -> a^2 = b^2 -> a = b := by
  intro ha hb sq_eq
  rw [expand_pow] at ha
  rw [expand_pow] at hb
  rw [sq_eq] at ha
  rw [← ha]
  exact hb

end
