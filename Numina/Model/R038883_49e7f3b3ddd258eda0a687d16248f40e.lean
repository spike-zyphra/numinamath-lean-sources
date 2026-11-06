import Mathlib

open Real

theorem inequalities_89096 {n : ℕ} (hn : 0 < n) (x y : ℝ)
    (hx : x = (1 + 1 / n : ℝ) ^ n) (hy : y = (1 + 1 / n : ℝ) ^ (n + 1)) :
    x ^ y = y ^ x := by 
  rw [hx, hy]
  have h1 : ((1 + (1 / n) : ℝ) ^ n : ℝ) ^ ((1 + (1 / n) : ℝ) ^ (n + 1) ) = (1 + (1 / n) : ℝ) ^ (n * ((1 + (1 / n) : ℝ) ^ (n + 1) ) ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_cast
    all_goals positivity
  have h2 : ((1 + (1 / n) : ℝ) ^ (n + 1) : ℝ) ^ ((1 + (1 / n) : ℝ) ^ n ) = (1 + (1 / n) : ℝ) ^ ((n + 1) * ((1 + (1 / n) : ℝ) ^ n ) ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_cast
    all_goals positivity
  rw [h1, h2]
  have h3 : n * ((1 + (1 / n) : ℝ) ^ (n + 1) ) = (n + 1) * ((1 + (1 / n) : ℝ) ^ n ) := by
    have h4 : ((1 + (1 / n) : ℝ) ^ (n + 1) ) = ((1 + (1 / n) : ℝ) ^ n ) * ((1 + (1 / n) : ℝ)) := by
      ring_nf
      <;> simp [pow_add]
      <;> ring
    rw [h4]
    field_simp at *
    <;> ring_nf
    <;> norm_num at *
    all_goals omega
  rw [h3]
  all_goals positivity