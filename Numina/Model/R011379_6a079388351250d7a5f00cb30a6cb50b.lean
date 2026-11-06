import Mathlib

theorem algebra_241109 {x : ℕ → ℝ} (hx : ∀ n, x n = n / (n + 2016)) :
    (4032, 6048) ∈ {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ x 2016 = x m * x n} := by
  constructor
  · norm_num
  constructor
  · norm_num
  · -- Show that x 2016 = x 4032 * x 6048
    rw [hx 2016, hx 4032, hx 6048]
    norm_num