import Mathlib

theorem algebra_255872 (x : ℝ) :
    Real.logb 2 (9^(x-1) + 7) = Real.logb 2 (3^(x-1) + 1) + 2 ↔
    x = 1 ∨ x = 2 := by
  constructor
  · -- Assume $\log_2(9^{x-1}+7) = \log_2(3^{x-1}+1)+2$, then $x = 1 \lor x = 2$.
    intro h_eq
    have h1 : Real.logb 2 (9^(x-1) + 7) = Real.logb 2 (3^(x-1) + 1) + 2 := h_eq
    have h2 : Real.logb 2 (9^(x-1) + 7) = Real.logb 2 ((3^(x-1) + 1) * (4 : ℝ)) := by
      have h3 : Real.logb 2 ((3^(x-1) + 1) * (4 : ℝ)) = Real.logb 2 (3^(x-1) + 1) + Real.logb 2 (4 : ℝ) := by 
        rw [Real.logb_mul (by positivity) (by positivity)]
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3, h4]
      linarith
    have h3 : (9 ^ (x - 1) + 7 : ℝ) = (3 ^ (x - 1) + 1) * (4 : ℝ) := by 
      have h4 : (9 ^ (x - 1) + 7 : ℝ) > 0 := by positivity
      have h5 : (3 ^ (x - 1) + 1 : ℝ) * (4 : ℝ) > 0 := by positivity
      have h6 : Real.logb 2 (9^ (x - 1) + 7) = Real.logb 2 ((3^ (x - 1) + 1) * (4 : ℝ)) := h2
      have h7 : (9^ (x - 1) + 7) = (3^ (x - 1) + 1) * (4 : ℝ) := by
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h5) h6
      linarith [h7]
    have h5 : (9 : ℝ) ^ (x - 1) = ((3 : ℝ) ^ (x - 1)) ^ 2 := by
      calc
        (9 : ℝ) ^ (x - 1) = (3 ^ (2 : ℝ) ) ^ (x - 1) := by norm_num
        _ = 3 ^ (2 * (x - 1) ) := by rw [← Real.rpow_mul]; ring_nf; all_goals norm_num
        _ = (3 ^ (x - 1) ) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring_nf; all_goals norm_num
    rw [h5] at h3
    have h6 : ((3 : ℝ) ^ (x - 1) ) ^ 2 - 4 * ((3 : ℝ) ^ (x - 1) ) + 3 = 0 := by
      nlinarith
      all_goals linarith
    have h7 : ((3 : ℝ) ^ (x - 1) - 3) * ((3 : ℝ) ^ (x - 1) - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case $((3 : ℝ) ^ (x - 1) - 3) = 0$
      have h8' : (3 : ℝ) ^ (x - 1) = 3 := by linarith
      have h10 : x - 1 = (1 : ℝ) := by
        apply_fun (Real.logb (3 : ℝ)) at h8'
        have h11 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (x - 1)) = x - 1 := by 
          rw [Real.logb_rpow]
          all_goals norm_num
        have h12 : Real.logb (3 : ℝ) (3 : ℝ) = 1 := by
          norm_num [Real.logb_eq_iff_rpow_eq]
        rw [h11, h12] at h8'
        linarith
      have h13 : x = 2 := by linarith 
      right
      exact h13
    · -- Case $((3 : ℝ) ^ (x - 1) - 1) = 0$
      have h9' : (3 : ℝ) ^ (x - 1) = 1 := by linarith
      have h14 : x - 1 = (0 : ℝ) := by
        apply_fun (Real.logb (3 : ℝ)) at h9'
        have h15 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (x - 1)) = x - 1 := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h16 : Real.logb (3 : ℝ) (1 : ℝ) = 0 := by 
          norm_num [Real.logb_eq_iff_rpow_eq]
        rw [h15, h16] at h9'
        linarith
      have h17 : x = 1 := by linarith 
      left
      exact h17
  · -- Assume x = 1 ∨ x = 2
    rintro (h | h)
    · -- Case x = 1
      rw [show x = (1 : ℝ) by linarith]
      have h2 : (9 : ℝ) ^ ((1 : ℝ) - 1 : ℝ) = 1 := by
        rw [show (9 : ℝ) ^ ((1 : ℝ) - 1 : ℝ) = (9 : ℝ) ^ (0 : ℝ) by norm_num]
        norm_num
      have h3 : (3 : ℝ) ^ ((1 : ℝ) - 1 : ℝ) = 1 := by
        rw [show (3 : ℝ) ^ ((1 : ℝ) - 1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
        norm_num
      rw [h2, h3]
      have h4 : Real.logb 2 (1 + 7 : ℝ) = Real.logb 2 (1 + 1 : ℝ) + 2 := by
        have h5 : Real.logb 2 (1 + 7 : ℝ) = 3 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        have h6 : Real.logb 2 (1 + 1 : ℝ) = 1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h5, h6]
      linarith [h4]
    · -- Case x = 2
      rw [show x = (2 : ℝ) by linarith]
      have h2 : (9 : ℝ) ^ ((2 : ℝ) - 1 : ℝ) = (9 : ℝ) := by
        rw [show (2 : ℝ) - 1 = (1 : ℝ) by norm_num]
        norm_num
      have h3 : (3 : ℝ) ^ ((2 : ℝ) - 1 : ℝ) = (3 : ℝ) := by
        rw [show (2 : ℝ) - 1 = (1 : ℝ) by norm_num]
        norm_num
      rw [h2, h3]
      have h4 : Real.logb 2 (9 + 7 : ℝ) = Real.logb 2 (3 + 1 : ℝ) + 2 := by
        have h5 : Real.logb 2 (9 + 7 : ℝ) = 4 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        have h6 : Real.logb 2 (3 + 1 : ℝ) = 2 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h5, h6]
      linarith [h4]