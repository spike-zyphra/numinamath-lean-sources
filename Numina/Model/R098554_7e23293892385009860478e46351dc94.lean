import Mathlib

theorem algebra_188297 {x : ℝ} (hx : x > 0 ∧ x ≠ 1) :
    Real.logb x 9 + Real.logb (x ^ 2) 729 = 10 ↔ x = Real.sqrt 3 := by
  constructor
  · -- First direction: if the equation holds, then x = sqrt(3)
    intro h
    have hx1 : x > 0 := hx.1
    have hx2 : x ≠ 1 := hx.2
    have h1 : Real.logb x 9 = Real.log 9 / Real.log x := by 
      field_simp [Real.logb]
    have h2 : Real.logb (x ^ 2) 729 = Real.log 729 / Real.log (x ^ 2) := by 
      field_simp [Real.logb]
    have h3 : Real.log 9 = 2 * Real.log 3 := by 
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp [Real.log_pow]
    have h4 : Real.log 729 = 6 * Real.log 3 := by 
      rw [show (729 : ℝ) = 3 ^ 6 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    have h5 : Real.log (x ^ 2) = 2 * Real.log x := by 
      simp [Real.log_pow]
    rw [h1, h2] at h
    rw [h3] at h 
    rw [h4] at h 
    rw [h5] at h 
    have h6 : Real.log x ≠ 0 := by
      by_contra h7
      have h8 : Real.log x = 0 := by linarith
      have h9 : x = 1 := by
        rw [Real.log_eq_zero] at h8
        rcases h8 with (r | r | r)
        · linarith
        · linarith
        · linarith
      have h10 : x = 1 := h9
      have h11 : x ≠ 1 := hx2
      contradiction
    have eq1 : (2 * Real.log 3 / Real.log x) + (6 * Real.log 3 / (2 * Real.log x)) = 10 := by
      linarith
    have eq2 : (2 * Real.log 3 / Real.log x) + (6 * Real.log 3 / (2 * Real.log x)) = (5 * Real.log 3) / Real.log x := by
      field_simp [h6]
      ring
    rw [eq2] at eq1 
    have eq3 : Real.log x = (1 / 2) * Real.log 3 := by
      field_simp [h6] at eq1 ⊢
      linarith
    have eq4 : x = Real.sqrt 3 := by
      have h8 : Real.log x = (1 / 2) * Real.log 3 := eq3
      have h9 : x ^ 2 = 3 := by
        have h10 : Real.log (x ^ 2) = 2 * Real.log x := by 
          simp [Real.log_pow]
        have h11 : Real.log (x ^ 2) = Real.log 3 := by
          rw [h10, h8]
          ring
        have h13 : x ^ 2 = (3 : ℝ) := by 
          exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : x ^ 2 > (0 : ℝ))) (Set.mem_Ioi.mpr (show (3 : ℝ) > 0 by norm_num)) h11
        nlinarith 
      have h14 : x ≥ 0 := by linarith [hx1]
      have h15 : x = Real.sqrt 3 := by
        have h16 : x ^ 2 = (3 : ℝ) := h9
        have h17 : x = Real.sqrt (3 : ℝ) := by
          have h18 : x ≥ 0 := by linarith [hx1]
          have h19 : (Real.sqrt (3 : ℝ)) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
          nlinarith [h16, h19, h18, Real.sqrt_nonneg (3 : ℝ)]
        exact h17
      exact h15
    exact eq4
  · -- Second direction: if x = sqrt(3), then the equation holds
    intro h
    rw [h]
    have h1 : Real.logb (Real.sqrt 3) 9 = Real.log 9 / Real.log (Real.sqrt 3) := by 
      field_simp [Real.logb]
    have h2 : Real.logb ((Real.sqrt 3) ^ 2) 729 = Real.log 729 / Real.log ((Real.sqrt 3) ^ 2) := by 
      field_simp [Real.logb]
    have h3 : Real.log 9 = 2 * Real.log 3 := by 
      rw [show (9 : ℝ) = 3  ^ 2 by norm_num]
      simp [Real.log_pow]
    have h4 : Real.log 729 = 6 * Real.log 3 := by 
      rw [show (729 : ℝ) = 3  ^ 6 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    have h5 : Real.log (Real.sqrt 3) = (1 / 2) * Real.log 3 := by
      have h6 : Real.sqrt 3 = (3 : ℝ)  ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h6]
      simp [Real.log_rpow]
      all_goals linarith
    have h7 : Real.log ((Real.sqrt 3)  ^ 2) = Real.log 3 := by 
      have h8 : (Real.sqrt 3)  ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      rw [h8]
    rw [h1, h2]
    rw [h3, h4, h5, h7]
    have h8 : Real.log 3 ≠ 0 := by
      have h9 : (3 : ℝ) > 1 := by norm_num
      have h10 : Real.log 3 > 0 := by 
        exact Real.log_pos (by norm_num)
      linarith
    field_simp [h8]
    <;> nlinarith