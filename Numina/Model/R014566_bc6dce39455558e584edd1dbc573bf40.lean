import Mathlib

theorem algebra_319771 {n : ℕ} (hn : n > 0) (x y : ℝ)
    (hx : x = (1 + 1 / n : ℝ) ^ n) (hy : y = (1 + 1 / n : ℝ) ^ (n + 1)) :
    x ^ y = y ^ x := by
  rw [hx, hy]
  have h1 : ((1 + (1 / n : ℝ)) ^ n : ℝ) ^ ((1 + (1 / n : ℝ)) ^ (n + 1)) =
          (1 + (1 / n : ℝ)) ^ (n * ((1 + (1 / n : ℝ)) ^ (n + 1)) ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_cast
    all_goals positivity
  have h2 : ((1 + (1 / n : ℝ)) ^ (n + 1) : ℝ) ^ ((1 + (1 / n : ℝ)) ^ n) =
          (1 + (1 / n : ℝ)) ^ ((n + 1) * ((1 + (1 / n : ℝ)) ^ n)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_cast
    all_goals positivity
  rw [h1, h2]
  have h3 : n * ((1 + (1 / n : ℝ)) ^ (n + 1)) = (n + 1) * ((1 + (1 / n : ℝ)) ^ n) := by
    have eq1 : (1 + (1 / n : ℝ)) ^ (n + 1) = (1 + (1 / n : ℝ)) ^ n * (1 + (1 / n : ℝ)) := by
      ring_nf
    rw [eq1]
    have eq2 : (1 + (1 / n : ℝ)) = (n + 1) / (n : ℝ) := by
      field_simp
      <;> nlinarith
    rw [eq2]
    field_simp at *
    <;> ring
  have h4 : (1 + (1 / n : ℝ)) ^ (n * ((1 + (1 / n : ℝ)) ^ (n + 1)) ) = (1 + (1 / n : ℝ)) ^ ((n + 1) * ((1 + (1 / n : ℝ)) ^ n)) := by
    rw [show n * ((1 + (1 / n : ℝ)) ^ (n + 1)) = (n + 1) * ((1 + (1 / n : ℝ)) ^ n) by linarith [h3] ]
  exact h4