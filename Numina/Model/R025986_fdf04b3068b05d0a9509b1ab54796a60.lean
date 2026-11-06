import Mathlib

theorem algebra_147711 (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 ^ i - 1) = 2 ^ (n + 1) - n - 2 := by
  induction n with
  | zero =>
    all_goals simp [Finset.sum_range_succ]
    all_goals omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    cases n with
    | zero =>
      all_goals simp [pow_succ, pow_zero]
      all_goals omega
    | succ n =>
      simp [pow_succ, pow_zero, Finset.sum_range_succ] at *
      all_goals omega