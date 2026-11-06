import Mathlib

theorem number_theory_286342 (n : ℕ) (hn : n > 0) (h : 35 * n + 15 * (n - 1) + 61 * (n - 2) = 2024) :
    n = 548 := by
  cases n with
  | zero => linarith
  | succ n =>
    cases n with
    | zero => simp at h
    | succ n =>
      cases n with
      | zero => simp at h
      | succ n =>
        simp [Nat.add_assoc] at h
        omega