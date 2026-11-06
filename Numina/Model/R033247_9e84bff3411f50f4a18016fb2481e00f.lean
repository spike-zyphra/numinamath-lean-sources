import Mathlib

open Real

theorem algebra_9008 :
  IsGreatest {z | ∃ x y : ℝ, x + y + z = 3 ∧ x * y + y * z + z * x = 2} (2 / (sqrt 3) + 1):= by
  constructor
  · -- Show that 2 / sqrt(3) + 1 is indeed in the set.
    use (3 - Real.sqrt 3) / 3, (3 - Real.sqrt 3) / 3
    constructor
    · -- Show x + y + z = 3
      have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ))
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
    · -- Show x * y + y * z + z * x = 2
      have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ))
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
  · -- Show that 2 / sqrt(3) + 1 is the greatest element in the set
    intro z hz
    rcases hz with ⟨x, y, h1, h2⟩
    have h3 : (x + y) = 3 - z := by linarith
    have h4 : x * y = z ^ 2 - 3 * z + 2 := by
      have eq1 : x * y + (x + y) * z = 2 := by
        nlinarith
      rw [h3] at eq1
      nlinarith
    have h5 : (3 - z) ^ 2 - 4 * (z ^ 2 - 3 * z + 2) ≥ 0 := by
      have h6 : (x - y) ^ 2 ≥ 0 := by
        nlinarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 * z)]
    have h7 : -3 * z ^ 2 + 6 * z + 1 ≥ 0 := by
      nlinarith
    have h8 : z ≤ (3 + 2 * Real.sqrt 3) / 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num: (0 : ℝ) < (3 : ℝ)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (z - (3 + 2 * Real.sqrt 3) / 3), sq_nonneg (z - (3 - 2 * Real.sqrt 3) / 3)]
    have h9 : (2 / (Real.sqrt 3) + 1) = (3 + 2 * Real.sqrt 3) / 3 := by
      have h10 : Real.sqrt 3 > 0 := by positivity
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num: (0 : ℝ) < (3 : ℝ)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]