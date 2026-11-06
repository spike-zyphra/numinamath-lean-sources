import Mathlib

open Real

theorem algebra_317294 {f : ℝ → ℝ} (hf : ∀ x, f x = log ((1 - x) / (1 + x))) (x : ℝ)
    (hx : x ≠ -1) :
    f ((x ^ 3 + 3 * x) / (1 + 3 * x ^ 2)) = 3 * f x := by
  have h1 : f ((x ^ 3 + 3 * x) / (1 + 3 * x ^ 2)) = log ((1 - (x ^ 3 + 3 * x) / (1 + 3 * x ^ 2)) / (1 + (x ^ 3 + 3 * x) / (1 + 3 * x ^ 2))) := by
    rw [hf]
  have h2 : f x = log ((1 - x) / (1 + x)) := by
    rw [hf]

  rw [h1, h2]
  have h3 : (1 - (x ^ 3 + 3 * x) / (1 + 3 * x ^ 2)) / (1 + (x ^ 3 + 3 * x) / (1 + 3 * x ^ 2)) = ((1 - x) / (1 + x)) ^ 3 := by
    have hx2 : 1 + 3 * x ^ 2 ≠ 0 := by
      by_contra h'
      have : x ^ 2 = -1 / 3 := by nlinarith
      have : x ^ 2 ≥ 0 := sq_nonneg x
      nlinarith
      all_goals linarith
    field_simp [hx2]
    ring_nf
    <;> field_simp [(show 1 + x ≠ 0 by
      intro h'
      apply hx
      linarith
      ), hx2]
    <;> ring_nf
    <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_pos_of_ne_zero (show 1 + x ≠ 0 by
      intro h'
      apply hx
      linarith
    )]

  rw [h3]
  have h4 : log (((1 - x) / (1 + x)) ^ 3) = 3 * log ((1 - x) / (1 + x)) := by
    simp [log_pow]
    <;> ring_nf
    <;> field_simp [(show 1 + x ≠ 0 by
      intro h'
      apply hx
      linarith
    )]
    <;> ring_nf
    <;> linarith
  rw [h4]
  all_goals linarith
  all_goals linarith
  all_goals linarith