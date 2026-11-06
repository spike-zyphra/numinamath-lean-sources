import Mathlib

open Real

theorem algebra_188135 {x : ℝ} (hx : x > 2) :
    logb 10 8 - logb 10 (sqrt (x + 6)) = logb 10 16 - logb 10 (x - 2) ↔ x = 10 := by
  constructor
  · -- Assume the equation holds, prove x = 10
    intro h_eq
    have h1 : logb 10 8 - logb 10 (sqrt (x + 6)) = logb 10 (8 / (sqrt (x + 6))) := by
      rw [← logb_div (by norm_num) (by positivity)]
    have h2 : logb 10 16 - logb 10 (x - 2) = logb 10 (16 / (x - 2)) := by
      rw [← logb_div (by norm_num) (by linarith)]
    rw [h1, h2] at h_eq
    have h3 : 8 / (sqrt (x + 6)) = 16 / (x - 2) := by
      have h4 : logb 10 (8 / (sqrt (x + 6))) = logb 10 (16 / (x - 2)) := h_eq
      have h5 : 8 / (sqrt (x + 6)) > 0 := by positivity
      have h6 : 16 / (x - 2) > 0 := by
        apply div_pos
        norm_num
        linarith
      have h7 : logb 10 (8 / (sqrt (x + 6))) = logb 10 (16 / (x - 2)) := h_eq
      have h8 : 8 / (sqrt (x + 6)) = 16 / (x - 2) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h5) (Set.mem_Ioi.mpr h6) h7
      exact h8
    have h5 : sqrt (x + 6) > 0 := by
      apply sqrt_pos.mpr
      linarith
    have h6 : x - 2 > 0 := by linarith
    have h7 : 8 * (x - 2) = 16 * (sqrt (x + 6)) := by
      field_simp [h5, h6] at h3 ⊢
      nlinarith
    have h8 : x - 2 = 2 * (sqrt (x + 6)) := by
      nlinarith
    have h9 : (x - 2) ^ 2 = (2 * (sqrt (x + 6)) ) ^ 2 := by
      rw [h8]
    have h10 : (2 * (sqrt (x + 6)) ) ^ 2 = 4 * (x + 6) := by
      calc
        (2 * (sqrt (x + 6)) ) ^ 2 = 4 * ((sqrt (x + 6)) ^ 2) := by ring
        _ = 4 * (x + 6) := by
          rw [Real.sq_sqrt]
          linarith
    have h11 : (x - 2) ^ 2 = 4 * (x + 6) := by
      rw [h9, h10]
    have h12 : (x - 10) * (x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- x - 10 = 0
      linarith
    · -- x + 2 = 0
      nlinarith
  · -- Assume x = 10, prove the equation
    intro h_eq
    rw [h_eq]
    have h2 : sqrt (10 + 6) = (4 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : (10 - 2 : ℝ) = (8 : ℝ) := by
      norm_num
    rw [h2, h3]
    have h4 : logb 10 (8 : ℝ) - logb 10 (4 : ℝ) = logb 10 (8 / (4 : ℝ)) := by
      rw [← logb_div (by norm_num) (by norm_num)]
    have h5 : logb 10 (16 : ℝ) - logb 10 (8 : ℝ) = logb 10 (16 / (8 : ℝ)) := by
      rw [← logb_div (by norm_num) (by norm_num)]
    have h6 : (8 / (4 : ℝ)) = (2 : ℝ) := by norm_num
    have h7 : (16 / (8 : ℝ)) = (2 : ℝ) := by norm_num
    rw [h4, h5, h6, h7]
    all_goals linarith