import Mathlib

theorem algebra_240242 (y z : Fin 4 → ℝ)
    (hy : ∏ i, y i = 2048 ^ 4) (hz : ∏ i, z i = 8 ^ 4) :
    (∏ i, y i * z i) ^ ((1 : ℝ) / 8) = 128 := by 
  have h1 : ∏ i, y i * z i = (∏ i, y i) * (∏ i, z i) := by 
    simp [Finset.prod_mul_distrib]
    <;> ring
  rw [h1]
  rw [hy, hz]
  have h2 : (2048 ^ 4 * (8 ^ 4) : ℝ) = (2 ^ 56 : ℝ) := by
    norm_num
  rw [h2]
  have h3 : ((2 ^ 56 : ℝ) : ℝ) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ (7 : ℝ) := by
    have h4 : ((2 ^ 56 : ℝ) : ℝ) ^ ((1 : ℝ) / 8) = ((2 : ℝ) ^ (56 : ℝ) ) ^ ((1 : ℝ) / 8) := by 
      norm_cast
    rw [h4]
    have h5 : ((2 : ℝ) ^ (56 : ℝ) ) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ (7 : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h5]
    all_goals norm_num
  rw [h3]
  norm_num
  all_goals norm_num