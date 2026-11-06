import Mathlib

/- Compute: $0.\overline{7}-0.\overline{4}+0.\overline{2}$. Express your answer as a common fraction. -/
theorem algebra_20500 : ∑' (i : ℕ), (7 : ℝ) / 10 ^ (i + 1) - ∑' (i : ℕ), (4 : ℝ) / 10 ^ (i + 1) + ∑' (i : ℕ), (2 : ℝ) / 10 ^ (i + 1) = 5 / 9 := by
  -- 简化级数表达式
  have h1 : ∀ i : ℕ, (7 : ℝ) / 10 ^ (i + 1) = 7 * (1 / 10 ^ (i + 1)):= by
    intro i
    ring
  have h2 : ∀ i : ℕ, (4 : ℝ) / 10 ^ (i + 1) = 4 * (1 / 10 ^ (i + 1)):= by
    intro i
    ring
  have h3 : ∀ i : ℕ, (2 : ℝ) / 10 ^ (i + 1) = 2 * (1 / 10 ^ (i + 1)):= by
    intro i
    ring
  simp only [h1, h2, h3]
  rw [show ∑' (i : ℕ), (7 : ℝ) * (1 / 10 ^ (i + 1)) = 7 * ∑' (i : ℕ), 1 / 10 ^ (i + 1) by exact tsum_mul_left]
  rw [show ∑' (i : ℕ), (4 : ℝ) * (1 / 10 ^ (i + 1)) = 4 * ∑' (i : ℕ), 1 / 10 ^ (i + 1) by exact tsum_mul_left]
  rw [show ∑' (i : ℕ), (2 : ℝ) * (1 / 10 ^ (i + 1)) = 2 * ∑' (i : ℕ), 1 / 10 ^ (i + 1) by exact tsum_mul_left]
  have h4 : ∀ i : ℕ, (1 : ℝ) / 10 ^ (i + 1) = (1 / 10) * (1 / 10) ^ i:= by
    intro i
    ring_nf
  simp only [h4]
  -- 使用几何级数求和公式
  rw [show ∑' (i : ℕ), ((1 : ℝ) / 10) * (1 / 10) ^ i = (1 / 10) * ∑' (i : ℕ), (1 / 10) ^ i by exact tsum_mul_left]
  have g : |(1 : ℝ) / 10| < 1:= by
    rw [show |(1 : ℝ) / 10| = (1 : ℝ) / 10 by exact abs_of_pos (by linarith)]
    linarith
  have h5 : ∑' (i : ℕ), ((1 : ℝ) / 10) ^ i = (1 - 1 / 10)⁻¹:= tsum_geometric_of_abs_lt_one g
  rw [h5]
  norm_num
