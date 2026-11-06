import Mathlib

theorem algebra_2530 {x0 : ℝ} (hx0 : x0 ≠ 1) (hx : abs ((1 + x0) / 2) - abs (-x0) = 0) :
    x0 ^ 2 > x0 ∧ x0 > 2 * x0 := by
  have h_eq : abs ((1 + x0) / 2) = abs (-x0) := by
    linarith

  by_cases h1 : x0 ≥ 0
  · -- x0 ≥ 0
    by_cases h2 : (1 + x0) / 2 ≥ 0
    · -- (1 + x0) / 2 ≥ 0
      have h11 : abs ((1 + x0) / 2) = (1 + x0) / 2 := by
        rw [abs_of_nonneg h2]
      have h22 : abs (-x0) = x0 := by
        rw [abs_of_nonpos (by linarith)]
        all_goals linarith
      rw [h11, h22] at h_eq
      have h3 : x0 = 1 := by linarith
      contradiction
    · -- (1 + x0) / 2 < 0
      -- x0 < -1 contradict with x0 ≥ 0
      have h11 : abs ((1 + x0) / 2) = - ((1 + x0) / 2) := by
        rw [abs_of_neg (by linarith)]
      have h22 : abs (-x0) = x0 := by
        rw [abs_of_nonpos (by linarith)]
        all_goals linarith
      rw [h11, h22] at h_eq
      linarith
  · -- x0 < 0
    by_cases h2 : (1 + x0) / 2 ≥ 0
    · -- (1 + x0) / 2 ≥ 0
      have h11 : abs ((1 + x0) / 2) = (1 + x0) / 2 := by
        rw [abs_of_nonneg h2]
      have h22 : abs (-x0) = -x0 := by
        rw [abs_of_pos (by linarith)]
      rw [h11, h22] at h_eq
      have h0 : x0 = -1 / 3 := by linarith
      constructor
      · -- x0 ^ 2 > x0
        rw [h0]
        norm_num
      · -- x0 > 2 * x0
        rw [h0]
        norm_num
    · -- (1 + x0) / 2 < 0
      have h11 : abs ((1 + x0) / 2) = - ((1 + x0) / 2) := by
        rw [abs_of_neg (by linarith)]
      have h22 : abs (-x0) = -x0 := by
        rw [abs_of_pos (by linarith)]
      rw [h11, h22] at h_eq
      linarith