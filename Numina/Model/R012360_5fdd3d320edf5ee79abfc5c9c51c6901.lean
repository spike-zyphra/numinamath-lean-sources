import Mathlib

theorem algebra_311443 {a b c : ℝ} (h : a ≠ -b - c) (h' : b ≠ -a - c)
    (h'' : c ≠ -a - b) (h''' : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    ∃ k : ℤ, (1 / a + 1 / b + 1 / c) ^ (2 * k + 1) =
    1 / a ^ (2 * k + 1) + 1 / b ^ (2 * k + 1) + 1 / c ^ (2 * k + 1) ∧
    (1 / a ^ (2 * k + 1) + 1 / b ^ (2 * k + 1) + 1 / c ^ (2 * k + 1)) =
    1 / (a ^ (2 * k + 1) + b ^ (2 * k + 1) + c ^ (2 * k + 1)) := by
  use 0
  constructor
  · -- Show that (1/a + 1/b + 1/c)^(2 * 0 + 1) = 1/a^(2 * 0 + 1) + 1/b^(2 * 0 + 1) + 1/c^(2 * 0 + 1)
    norm_num
  · -- Show that (1/a^(2 * 0 + 1) + 1/b^(2 * 0 + 1) + 1/c^(2 * 0 + 1)) = 1 / (a^(2 * 0 + 1) + b^(2 * 0 + 1) + c^(2 * 0 + 1))
    norm_num at h''' ⊢
    all_goals
      linarith