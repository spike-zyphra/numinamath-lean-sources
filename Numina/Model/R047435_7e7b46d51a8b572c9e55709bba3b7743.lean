import Mathlib

theorem algebra_255827 :
    {(x, y) : ℝ × ℝ | x ≥ y ∧ y ≥ 0 ∧ x ^ 2 - y ^ 2 = 9 ∧ Real.sqrt (x + y) - Real.sqrt (x - y) = Real.sqrt y} = {(5, 4), (3, 0)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward direction: from the properties to the solutions
    rintro ⟨hxy, hy, h1, h2⟩
    have h3 : x ≥ y := hxy
    have h4 : y ≥ 0 := hy
    have h5 : x ^ 2 - y ^ 2 = 9 := h1
    have h6 : Real.sqrt (x + y) - Real.sqrt (x - y) = Real.sqrt y := h2
    have h7 : (Real.sqrt (x + y) - Real.sqrt (x - y))^2 = (Real.sqrt y)^2 := by
      rw [h6]
    have h61 : Real.sqrt (x + y) ^2 = x + y := by 
      apply Real.sq_sqrt
      nlinarith
    have h62 : Real.sqrt (x - y) ^2 = x - y := by 
      apply Real.sq_sqrt
      nlinarith
    have h63 : Real.sqrt y ^2 = y := by
      apply Real.sq_sqrt 
      nlinarith
    have h8 : (Real.sqrt (x + y) - Real.sqrt (x - y))^2 = 
          (Real.sqrt (x + y))^2 + (Real.sqrt (x - y))^2 - 2 * (Real.sqrt (x + y) * Real.sqrt (x - y)) := by 
        ring
    rw [h8] at h7 
    rw [h61, h62, h63] at h7
    have h15 : (Real.sqrt (x + y) * Real.sqrt (x - y)) = 3 := by 
      have h22 : Real.sqrt (x + y) * Real.sqrt (x - y) = Real.sqrt ((x + y) * (x - y)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      have h23 : (x + y) * (x - y) = 9 := by 
        nlinarith 
      rw [h22]
      have h28 : Real.sqrt ((x + y) * (x - y)) = 3 := by
        rw [h23]
        have h29 : Real.sqrt (9 : ℝ) = 3 := by
          rw [Real.sqrt_eq_cases]
          all_goals norm_num
        linarith 
      linarith
    have eq3 : y = 2*x - 6 := by 
      nlinarith [h7, h15]
    -- Now we need to solve the quadratic
    have h10 : x ^ 2 - (2 * x - 6) ^ 2 = 9 := by
      have eq4 : y = 2*x - 6 := eq3 
      rw [eq4] at h1 
      linarith
    have h11 : (x - 5) * (x - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- x -5 =0
      have hx : x = 5 := by linarith
      -- Then y must be 4
      have hy4 : y = 4 := by 
        linarith [eq3, hx]
      left
      exact ⟨hx, hy4⟩
    · -- x -3 =0
      have hx : x = 3 := by linarith
      -- Then y must be 0
      have hy0 : y = 0 := by 
        linarith [eq3, hx]
      right
      exact ⟨hx, hy0⟩
  · -- Backward direction: from the solutions to the properties
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- First solution: (5, 4)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that sqrt(5+4) - sqrt(5-4) = sqrt(4)
        have h1 : Real.sqrt (5 + 4) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h2 : Real.sqrt (5 - 4) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h3 : Real.sqrt (4 : ℝ) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h1, h2, h3]
        all_goals norm_num
    · -- Second solution: (3, 0)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show that sqrt(3+0) - sqrt(3-0) = sqrt(0)
        have h1 : Real.sqrt (3 + 0) = Real.sqrt 3 := by
          norm_num
        have h2 : Real.sqrt (3 - 0) = Real.sqrt 3 := by
          norm_num
        have h3 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
        rw [h1, h2, h3]
        all_goals norm_num