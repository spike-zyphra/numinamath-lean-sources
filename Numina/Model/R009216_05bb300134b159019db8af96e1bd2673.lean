import Mathlib

/- define the answer to the problem -/
def Solution : ℕ → ℕ := fun n => match n with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 6 => 2
  | 14 => 6
  | 24 => 8
  | n => Nat.totient n

theorem number_theory_4864 : (n=1 ∨ n=2 ∨ n=3 ∨ n=6 ∨ n=14 ∨ n=24) →
    (Nat.totient n = Solution n) := by
  intro h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    rfl