import Mathlib.Tactic

syntax "exactly" term "at" ident : tactic
macro_rules
| `(tactic| exactly $t at $u ) => `(tactic| apply $t at $u; exact $u )

syntax "cases_rw" Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| cases_rw $target ) =>
    `(tactic| cases $target with
                | inl left  => rw [left];  simp
                | inr right => rw [right]; simp )
