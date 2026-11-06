import Mathlib

theorem number_theory_73551 {x y z : ℤ} (h1 : x ^ 2 = y * z + 1) (h2 : y ^ 2 = z * x + 1)
    (h3 : z ^ 2 = x * y + 1) :
    (x, y, z) = (1, 0, -1) ∨ (x, y, z) = (-1, 0, 1) ∨ (x, y, z) = (0, 1, -1) ∨
    (x, y, z) = (0, -1, 1) ∨ (x, y, z) = (-1, 1, 0) ∨ (x, y, z) = (1, -1, 0) := by
  have h4 : (x - y) * (x + y + z) = 0 := by
    nlinarith 
  have h5 : (y - z) * (x + y + z) = 0 := by 
    nlinarith 
  by_cases h : x + y + z = 0 
  · -- Assume x + y + z = 0
    have h7 : z = -x - y := by 
      linarith 
    rw [h7] at h1 h2 h3 
    have h8 : x ^ 2 + x * y + y ^ 2 = 1 := by 
      nlinarith 
    have h9 : x ≤ 1 := by 
      nlinarith [sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x - y)]
    have h10 : x ≥ -1 := by 
      nlinarith [sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x - y)]
    have h11 : y ≤ 1 := by 
      nlinarith [sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y - x)]
    have h12 : y ≥ -1 := by 
      nlinarith [sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y - x)]
    interval_cases x <;> interval_cases y 
    <;> norm_num at h8 
    <;> norm_num [h7, Prod.ext_iff] at *
    <;> omega 
  · -- Assume x + y + z ≠ 0
    have h4' : (x - y) = 0 := by 
      apply_fun (fun w => w / (x + y + z)) at h4 
      field_simp [show x + y + z ≠ 0 by 
        omega 
      ] at h4 
      all_goals linarith 
    have h9 : x = y := by 
      linarith 
    have h10' : (y - z) = 0 := by 
      apply_fun (fun w => w / (x + y + z)) at h5 
      field_simp [show x + y + z ≠ 0 by 
        omega 
      ] at h5 
      all_goals linarith 
    have h11 : y = z := by 
      linarith 
    have h12 : x = z := by 
      linarith 
    -- $x = y = z$ leads to a contradiction
    have h13 : x^2 = x * x + 1 := by 
      have h14 : y = x := by linarith 
      rw [h14] at h1 
      have h15 : z = x := by linarith 
      rw [h15] at h1 
      linarith 
    nlinarith