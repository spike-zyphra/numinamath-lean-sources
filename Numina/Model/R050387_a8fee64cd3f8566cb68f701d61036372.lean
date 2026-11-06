import Mathlib

theorem number_theory_213083 {n : ℕ} (hn : n > 0) (h : n * 3 = 7 * (n - 1)) :
    n = 9 := by
  cases n with
  | zero =>
    linarith
  | succ n =>
    simp [Nat.mul_add, Nat.mul_assoc, Nat.sub_add_cancel] at h ⊢
    all_goals
      omega