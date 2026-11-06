import Mathlib

theorem algebra_604130 {x y : ℝ} {n : ℕ} (hn : n ≠ 0) (hx : x = (1 + 1 / n) ^ n)
    (hy : y = (1 + 1 / n) ^ (n + 1)) : y ^ x = x ^ y := by 
  rw [hx, hy]
  have h1 : ((1 + (1 / (n : ℝ))) ^ (n + 1 : ℕ)) ^ ((1 + (1 / (n : ℝ))) ^ (n : ℕ) : ℝ) =
      (1 + (1 / (n : ℝ)) : ℝ) ^ ((n + 1 : ℝ) * ((1 + (1 / (n : ℝ))) ^ (n : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_cast
    all_goals positivity
  have h2 : ((1 + (1 / (n : ℝ))) ^ (n : ℕ) : ℝ) ^ ((1 + (1 / (n : ℝ))) ^ (n + 1 : ℕ) : ℝ) =
      (1 + (1 / (n : ℝ)) : ℝ) ^ ((n : ℝ) * ((1 + (1 / (n : ℝ))) ^ (n + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_cast
    all_goals positivity
  have h3 : (n + 1 : ℝ) * ((1 + (1 / (n : ℝ))) ^ (n : ℕ) : ℝ) =
      (n : ℝ) * ((1 + (1 / (n : ℝ))) ^ (n + 1 : ℕ) : ℝ) := by
    have h4 : (1 + (1 / (n : ℝ))) ^ (n + 1 : ℕ) = ((1 + (1 / (n : ℝ))) ^ (n : ℕ) : ℝ) * ((1 + (1 / (n : ℝ)) : ℝ)) := by
      ring_nf
      <;> simp [pow_succ]
      <;> ring
    rw [h4]
    field_simp at *
    <;> ring_nf
  rw [h1, h2]
  rw [h3]
  all_goals norm_num
  all_goals positivity
  all_goals norm_cast
  all_goals tauto