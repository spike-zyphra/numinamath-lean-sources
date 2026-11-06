import Mathlib

theorem algebra_188022 (x : ℝ) (hx : x > 0) :
    x ^ (Real.logb 4 x - 2) = 2 ^ (3 * (Real.logb 4 x - 1)) ↔ x = 2 ∨ x = 64 := by
  constructor
  · -- Assume x ^ (Real.logb 4 x - 2) = 2 ^ (3 * (Real.logb 4 x - 1)), prove x = 2 ∨ x = 64
    intro h_eq
    have h3 : Real.log (x ^ (Real.logb 4 x - 2)) = Real.log (2 ^ (3 * (Real.logb 4 x - 1))) := by
      rw [h_eq]
    have h4 : Real.log (x ^ (Real.logb 4 x - 2)) = (Real.logb 4 x - 2) * Real.log x := by
      rw [Real.log_rpow]
      all_goals linarith
    have h5 : Real.log (2 ^ (3 * (Real.logb 4 x - 1))) = (3 * (Real.logb 4 x - 1)) * Real.log 2 := by
      rw [Real.log_rpow]
      all_goals norm_num
    rw [h4, h5] at h3
    have h6 : (Real.logb 4 x - 2) * Real.log x = (3 * (Real.logb 4 x - 1)) * Real.log 2 := by linarith
    have h7 : Real.logb 4 x = Real.log x / Real.log 4 := by
      field_simp [Real.logb]
    rw [h7] at h6
    have h8 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    rw [h8] at  h6
    have h6' : (Real.log x / (2 * Real.log 2) - 2) * Real.log x = (3 * (Real.log x / (2 * Real.log 2) - 1)) * Real.log 2 := by
      linarith
    have h10 : Real.log 2 > 0 := by
      apply Real.log_pos
      norm_num
    have h12 : (Real.log x - Real.log 2) * (Real.log x - 6 * Real.log 2) = 0 := by
      field_simp at h6' ⊢
      nlinarith [h10]
    have h13 : Real.log x = Real.log 2 ∨ Real.log x = 6 * Real.log 2 := by
      cases (mul_eq_zero.mp h12) with
      | inl h14 => 
        left; linarith
      | inr h15 =>
        right; linarith
    cases h13 with
    | inl h14 =>
      have h15 : x = 2 := by
        have h16 : Real.log x = Real.log 2 := h14
        have h17 : x > 0 := by linarith
        have h18 : (2 : ℝ) > 0 := by norm_num
        have h19 : x = 2 := by
          apply Real.log_injOn_pos (Set.mem_Ioi.mpr h17) (Set.mem_Ioi.mpr h18) h16
        linarith
      left; linarith
    | inr h15 =>
      have h16 : Real.log x = 6 * Real.log 2 := h15
      have h17 : x = 64 := by
        have h18 : Real.log x = 6 * Real.log 2 := h16
        have h19 : Real.log x = Real.log (64 : ℝ) := by
          have h20 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
            calc
              Real.log (64 : ℝ) = Real.log (2 ^ 6) := by norm_num
              _ = 6 * Real.log 2 := by simp [Real.log_pow]
          linarith [h20, h18]
        have h21 : x > 0 := by linarith
        have h22 : (64 : ℝ) > 0 := by norm_num
        have h23 : x = 64 := by
          apply Real.log_injOn_pos (Set.mem_Ioi.mpr h21) (Set.mem_Ioi.mpr h22) h19
        linarith
      right; linarith
  · -- Assume x = 2 ∨ x = 64, prove x ^ (Real.logb 4 x - 2) = 2 ^ (3 * (Real.logb 4 x - 1))
    rintro (h_eq | h_eq)
    · -- x = 2
      rw [h_eq]
      have h1 : Real.logb 4 (2 : ℝ) = 1 / 2 := by
        rw [Real.logb]
        have h2 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
          calc
            Real.log (4 : ℝ) = Real.log (2 ^ 2 : ℝ) := by norm_num
            _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
        field_simp [h2]
        <;> nlinarith
      rw [h1]
      norm_num
    · -- x = 64
      rw [h_eq]
      have h1 : Real.logb 4 (64 : ℝ) = 3 := by
        rw [Real.logb]
        have h2 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
          calc
            Real.log (4 : ℝ) = Real.log (2 ^ 2 : ℝ) := by norm_num
            _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
        have h3 : Real.log (64 : ℝ) = 6 * Real.log (2 : ℝ) := by
          calc
            Real.log (64 : ℝ) = Real.log (2 ^ 6 : ℝ) := by norm_num
            _ = 6 * Real.log (2 : ℝ) := by simp [Real.log_pow]
        rw [h2, h3]
        field_simp [show Real.log (2 : ℝ) ≠ 0 by apply ne_of_gt; apply Real.log_pos; norm_num]
        <;> nlinarith
      rw [h1]
      norm_num