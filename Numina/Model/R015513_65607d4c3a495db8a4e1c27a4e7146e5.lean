import Mathlib

open Real

theorem algebra_153594 {x : ℝ} (hx : x > 1) :
    logb 4 (x + 3) - logb 4 (x - 1) = 2 - 3 * logb 4 2 ↔ x = 5 := by
  constructor
  · -- Assume the equation holds, prove x = 5
    intro h_eq
    have h1 : logb 4 (x + 3) - logb 4 (x - 1) = logb 4 ((x + 3) / (x - 1)) := by
      rw [← logb_div (by linarith) (by linarith)]
    rw [h1] at h_eq
    have h2 : logb 4 ((x + 3) / (x - 1)) = logb 4 2 := by
      have h3 : (2 - 3 * logb 4 2) = logb 4 2 := by
        have h4 : logb 4 2 = 1 / 2 := by
          rw [logb]
          have : log 4 = 2 * log 2 := by
            calc
              log 4 = log (2 ^ 2) := by norm_num
              _ = 2 * log 2 := by simp [log_pow]
              _ = 2 * log 2 := by ring
          field_simp [this]
          <;> try ring
        rw [h4]
        linarith
      linarith [h_eq, h3]
    have h3 : (x + 3) / (x - 1) = 2 := by
      have h4 : logb 4 ((x + 3) / (x - 1)) = logb 4 2 := h2
      have h5 : ((x + 3) / (x - 1) : ℝ) > 0 := by
        apply div_pos
        linarith
        linarith
      have h6 : (2 : ℝ) > 0 := by norm_num
      have h7 : ( (x + 3) / (x - 1) ) = (2 : ℝ) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h5) (Set.mem_Ioi.mpr h6) h4
      linarith
    have h4 : x = 5 := by
      have h5 : (x - 1) ≠ 0 := by
        linarith
      field_simp at h3
      nlinarith
    exact h4
  · -- Assume x = 5, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : logb 4 (5 + 3 : ℝ) - logb 4 (5 - 1 : ℝ) = logb 4 ((5 + 3 : ℝ) / (5 - 1 : ℝ)) := by
      rw [← logb_div (by norm_num) (by norm_num)]
    have h2 : logb 4 ((5 + 3 : ℝ) / (5 - 1 : ℝ)) = logb 4 2 := by
      have h3 : ((5 + 3 : ℝ) / (5 - 1 : ℝ)) = (2 : ℝ) := by
        norm_num
      rw [h3]
    rw [h1, h2]
    have h4 : (2 - 3 * logb 4 2) = logb 4 2 := by
      have h4 : logb 4 2 = 1 / 2 := by
        rw [logb]
        have : log 4 = 2 * log 2 := by
          calc
            log 4 = log (2 ^ 2) := by norm_num
            _ = 2 * log 2 := by simp [log_pow]
            _ = 2 * log 2 := by ring
        field_simp [this]
        <;> try ring
      rw [h4]
      linarith
    linarith [h4]