import Mathlib

theorem algebra_186929 (x : ℝ) : (9 : ℝ)^(x - 1) + 3^(x + 2) = 90 ↔ x = 2 := by
  constructor
  · -- Assume (9 : ℝ)^(x - 1) + 3^(x + 2) = 90, prove x = 2
    intro h
    have h1 : (9 : ℝ) ^ (x - 1) = (3 : ℝ) ^ (2 * (x - 1)) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h1] at h
    have h2 : (3 : ℝ) ^ (2 * (x - 1)) = ((3 : ℝ) ^ x) ^ 2 / 9 := by
      have h3 : (3 : ℝ) ^ (2 * (x - 1)) = ((3 : ℝ) ^ (2 * x - 2)) := by ring_nf
      rw [h3]
      have h4 : (3 : ℝ) ^ (2 * x - 2) = ((3 : ℝ) ^ (2 * x)) / ((3 : ℝ) ^ (2 : ℝ)) := by 
        rw [← Real.rpow_sub]
        ring_nf
        all_goals norm_num
      rw [h4]
      have h5 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by 
        calc
          (3 : ℝ) ^ (2 * x) = (3 : ℝ) ^ (2 * x) := by rfl
          _ = ((3 : ℝ) ^ x) ^ 2 := by 
            calc
              (3 : ℝ) ^ (2 * x) = (3 : ℝ) ^ (x + x) := by ring
              _ = ((3 : ℝ) ^ x) * ((3 : ℝ) ^ x) := by rw [← Real.rpow_add]; ring_nf; all_goals norm_num
              _ = ((3 : ℝ) ^ x) ^ 2 := by ring
      rw [h5]
      norm_num
    have h3 : (3 : ℝ) ^ (x + 2) = 9 * (3 : ℝ) ^ x := by 
      calc
        (3 : ℝ) ^ (x + 2) = (3 : ℝ) ^ x * (3 : ℝ) ^ (2 : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf
          all_goals norm_num
        _ = (3 : ℝ) ^ x * (9 : ℝ) := by 
          norm_num
        _ = 9 * (3 : ℝ) ^ x := by 
          ring
    rw [h2, h3] at h
    have h4 : ((3 : ℝ) ^ x) ^ 2 + 81 * (3 : ℝ) ^ x = 810 := by
      field_simp at h ⊢
      nlinarith
    have h5 : ((3 : ℝ) ^ x) ^ 2 + 81 * (3 : ℝ) ^ x - 810 = 0 := by linarith
    have h6 : ((3 : ℝ) ^ x - 9) * ((3 : ℝ) ^ x + 90) = 0 := by 
      nlinarith [h5]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case $3^x - 9 = 0$, so $3^x = 9$
      have h3x9 : (3 : ℝ) ^ x = (9 : ℝ) := by 
        linarith
      have h8 : x = (2 : ℝ) := by
        apply_fun (Real.logb (3 : ℝ)) at h3x9
        have h9 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = x := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h10 : Real.logb (3 : ℝ) (9 : ℝ) = (2 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h9, h10] at h3x9 
        linarith
      linarith
    · -- Case $3^x + 90 = 0$, so $3^x = -90$
      have h3x9 : (3 : ℝ) ^ x = (-90 : ℝ) := by
        linarith
      have h10 : (3 : ℝ) ^ x > 0 := by
        positivity
      nlinarith
  · -- Assume x = 2, prove (9 : ℝ)^(x - 1) + 3^(x + 2) = 90
    intro h
    rw [h]
    norm_num