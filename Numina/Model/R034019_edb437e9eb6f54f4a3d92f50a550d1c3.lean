import Mathlib

theorem algebra_98011 (x b : ℝ) (hx : x > 1) (hb: b ≥ 2)
(h1 : 3 * Real.logb b (Real.sqrt x * Real.logb b x) = 56)
(h2 : Real.logb (Real.logb b x) x = 54) (h2' : 0 < Real.logb b x) (h2'': Real.logb b x ≠ 1)
: b = 216 := by
  have hb2 : b > 0 := by nlinarith
  have hb3 : b ≠ 1 := by nlinarith
  have h3_pos : Real.logb b x > 0 := by
    apply Real.logb_pos
    all_goals nlinarith
  
  have h_eq1 : Real.logb (Real.logb b x) x = Real.log x / Real.log (Real.logb b x) := by 
    field_simp [Real.logb]
    all_goals nlinarith
  rw [h_eq1] at h2
  
  have h_eq2 : Real.log x = Real.logb b x * Real.log b := by 
    have h4 : Real.log x = Real.logb b x * Real.log b := by
      have h5 : Real.logb b x = Real.log x / Real.log b := by 
        field_simp [Real.logb]
        all_goals nlinarith
      have h8 : Real.log b ≠ 0 := by
        by_contra h0
        have h9 : Real.logb b x = 0 := by
          rw [h5]
          field_simp [h0] at *
        linarith [h9, h3_pos]
      field_simp [h5] at *
      all_goals nlinarith
    linarith
  
  have h_eq3 : 3 * Real.logb b (Real.sqrt x * Real.logb b x) = 3 * (Real.logb b (Real.sqrt x) + Real.logb b (Real.logb b x)) := by
    have h_eq3' : Real.logb b (Real.sqrt x * Real.logb b x) = Real.logb b (Real.sqrt x) + Real.logb b (Real.logb b x) := by
      rw [Real.logb_mul (by positivity) (by positivity)]
    linarith [h_eq3']
  rw [h_eq3] at h1
  
  have h_eq4 : Real.logb b (Real.sqrt x) = (1 / 2) * Real.logb b x := by
    have h5 : Real.logb b (Real.sqrt x) = (1 / 2) * Real.logb b x := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals nlinarith
    linarith
  
  have h_eq5 : Real.logb b (Real.logb b x) = Real.log (Real.logb b x) / Real.log b := by
    field_simp [Real.logb]
    all_goals nlinarith
  
  have eq1' : 3 * ((1 / 2) * Real.logb b x + (Real.log (Real.logb b x) / Real.log b)) = 56 := by
    have eq1' : Real.logb b (Real.sqrt x) = (1 / 2) * Real.logb b x := h_eq4
    have eq5' : Real.logb b (Real.logb b x) = Real.log (Real.logb b x) / Real.log b := h_eq5
    have h_eq3' : 3 * (Real.logb b (Real.sqrt x) + Real.logb b (Real.logb b x)) = 3 * ((1 / 2) * Real.logb b x + (Real.log (Real.logb b x) / Real.log b)) := by
      rw [eq1', eq5']
      all_goals nlinarith
    linarith [h_eq3']
  
  have h_eq6 : Real.log x = 54 * Real.log (Real.logb b x) := by
    have h_ne : Real.log (Real.logb b x) ≠ 0 := by
      by_contra h
      have h_zero : Real.log (Real.logb b x) = 0 := by linarith
      have h1_pos : Real.logb b x = 1 := by
        have h6 : Real.log (Real.logb b x) = 0 := h_zero
        rw [Real.log_eq_zero] at h6
        rcases h6 with (r | r | r)
        · -- Real.logb b x = 1
          linarith
        · -- Real.logb b x = 1
          linarith
        · -- Real.logb b x = 1
          linarith
      exfalso
      exact h2'' h1_pos
    have eq2'' : Real.log x = 54 * Real.log (Real.logb b x) := by
      field_simp [h_ne] at h2 ⊢
      nlinarith
      all_goals nlinarith
    linarith
  
  have hy1 : Real.logb b x = 36 := by
    have h5_pos : Real.log b > 0 := by
      apply Real.log_pos
      all_goals nlinarith
    have h6 : Real.logb b x > 0 := h3_pos
    ring_nf at eq1'
    field_simp [h5_pos] at eq1' h_eq6 h_eq2
    nlinarith [sq_nonneg (Real.log (Real.logb b x) * 3), sq_nonneg (Real.log (Real.logb b x) - Real.log 36), sq_nonneg (Real.log b - Real.log (6 : ℝ) * 3 / 2), sq_pos_of_pos h5_pos, sq_pos_of_pos h6, Real.log_pos (show (6 : ℝ) > 1 by norm_num), Real.log_pos (show (36 : ℝ) > 1 by norm_num)]
  
  -- Once we know Real.logb b x = 36, we can derive b = 216
  have h5_pos : Real.log b > 0 := by
    apply Real.log_pos
    all_goals nlinarith
  
  have h8 : Real.log (Real.logb b x) = Real.log (36 : ℝ) := by
    have eq3'' : Real.logb b x = 36 := hy1
    rw [eq3'']

  have h9 : b = 216 := by
    have h10 : Real.log b = (3 / 2) * Real.log (36 : ℝ) := by
      nlinarith [sq_nonneg (Real.logb b x - 36), sq_pos_of_pos h5_pos, sq_pos_of_pos h3_pos, h_eq2, h_eq6, Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (4 : ℝ) > 1 by norm_num)]
    
    have h31 : Real.log 216 = (3 / 2) * Real.log (36 : ℝ) := by
      have h27 : Real.log (216 : ℝ) = 3 * Real.log (6 : ℝ) := by
        calc
          Real.log (216 : ℝ) = Real.log (6 ^ 3) := by norm_num
          _ = 3 * Real.log (6 : ℝ) := by
            simp [Real.log_pow]
      
      have h28 : Real.log (36 : ℝ) = 2 * Real.log (6 : ℝ) := by
        calc
          Real.log (36 : ℝ) = Real.log (6 ^ 2) := by norm_num
          _ = 2 * Real.log (6 : ℝ) := by
            simp [Real.log_pow]

      have h32 : (3 / 2) * Real.log (36 : ℝ) = 3 * Real.log (6 : ℝ) := by
          linarith

      linarith

    have h38 : Real.log b = Real.log 216 := by
      nlinarith [Real.log_pos (show (216 : ℝ) > 1 by norm_num), sq_pos_of_pos h5_pos]

    have h39 : b = (216 : ℝ) := by
      have hb2_pos : b > 0 := by nlinarith
      have h216_pos : (216 : ℝ) > 0 := by norm_num
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hb2_pos) (Set.mem_Ioi.mpr h216_pos) h38

    assumption
  
  assumption