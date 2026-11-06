import Mathlib

theorem algebra_122866 {b c : ℕ} (hb : 0 < b) (hc : 0 ≤ c ∧ c ≤ b - 1)
    (a : ℕ → ℤ) (ha1 : a 1 = b * (b + 1) / 2 + c)
    (han : ∀ n ≥ 1, a (n + 1) = if a n ≤ n then a n + n else a n - n) :
    ∃ T : ℕ → ℤ, T 1 = b + 2 * c ∧ ∀ m ≥ 1, T m = ((2 * b + 4 * c - 1) * 3 ^ (m - 1) + 1) / 2 := by
  use fun m => ((2 * b + 4 * c - 1) * 3 ^ (m - 1) + 1) / 2
  constructor
  · -- Verify T 1 = b + 2 * c
    norm_num
    <;> omega
  · -- Verify for all m ≥ 1, T m = ((2 * b + 4 * c - 1) * 3 ^ (m - 1) + 1) / 2
    intro m hm
    all_goals norm_num