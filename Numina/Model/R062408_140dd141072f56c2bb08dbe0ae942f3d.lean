import Mathlib

open Real

theorem algebra_9535 {x : ℝ} (hx : 0 < x) (hx1 : 205 - 35 * x > 0) :
    logb 5 (205 - 35 * x) - logb 5 x = 3 ↔ x = 1 + 9 / 32 := by
  constructor
  · -- Assume logb 5 (205 - 35 * x) - logb 5 x = 3 prove x = 1 + 9 / 32
    intro h
    have h1 : logb 5 (205 - 35 * x) - logb 5 x = logb 5 ((205 - 35 * x) / x) := by
      rw [← logb_div (by linarith) (by linarith)]
    rw [h1] at h
    have h2 : (205 - 35 * x) / x = (5 : ℝ) ^ (3 : ℝ) := by
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by 
        positivity
      )] at h 
      all_goals nlinarith
    have h3 : (205 - 35 * x) / x = (125 : ℝ) := by
      norm_num at h2 ⊢
      linarith
    have h4 : 205 - 35 * x = 125 * x := by
      have hx2 : x ≠ 0 := by linarith
      field_simp at h3
      nlinarith
    have h5 : 160 * x = 205 := by
      linarith [h4]
    have h6 : x = (41 / 32 : ℝ) := by
      linarith
    rw [h6]
    all_goals norm_num
  · -- Assume x = 1 + 9/32 prove logb 5 (205 - 35 * x) - logb 5 x = 3
    intro h
    rw [h]
    have h1 : (205 - 35 * (1 + (9 / 32 : ℝ))) = (5125 / 32 : ℝ) := by
      norm_num
    have h2 : (1 + (9 / 32 : ℝ) ) = (41 / 32 : ℝ) := by
      norm_num
    rw [h1, h2]
    have h3 : (5125 / 32 : ℝ) / (41 / 32 : ℝ) = (125 : ℝ) := by
      field_simp
      <;> norm_num
    have h4 : logb 5 ((5125 / 32 : ℝ) / (41 / 32 : ℝ)) = 3 := by
      rw [h3]
      have h5 : logb 5 (125 : ℝ) = 3 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
        all_goals norm_num
      linarith
    have h6 : logb 5 (5125 / 32 : ℝ) - logb 5 (41 / 32 : ℝ) = logb 5 ((5125 / 32 : ℝ) / (41 / 32 : ℝ)) := by
      rw [← logb_div (by positivity) (by positivity)]
    linarith [h6, h4]