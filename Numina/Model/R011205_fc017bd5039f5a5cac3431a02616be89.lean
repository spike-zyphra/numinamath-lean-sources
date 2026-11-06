import Mathlib
theorem algebra_611433 : IsGreatest {a : ℝ | ∃ x > 1, a = (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1)} (1 / 6):= by 
  constructor 
  -- Prove the value is achievable, using x = (1 + sqrt(5)) / 2 
  · use (1 + Real.sqrt 5) / 2 
    constructor 
    -- Show the value is greater than 1 
    · -- Show that (1 + sqrt 5) / 2 > 1 
      have h1 : 1 + Real.sqrt 5 > 2 := by 
        have h2 : Real.sqrt 5 > 1 := by 
          have h3 : Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num) 
          have h4 : Real.sqrt 1 = 1 := Real.sqrt_one 
          linarith 
        linarith 
      linarith 
    -- Compute the value 
    · -- Show that ((1 + sqrt 5) / 2)^4 - (1 + sqrt 5) / 2)^2) / (((1 + sqrt 5) / 2)^6 + 2 * ((1 + sqrt 5) / 2)^3 - 1) = 1 / 6 
      have hx1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (3 + Real.sqrt 5) / 2 := by 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
      have hx2 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 = 2 + Real.sqrt 5 := by 
        have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (3 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
        calc 
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 
            = ((1 + Real.sqrt 5) / 2 : ℝ) * ((1 + Real.sqrt 5) / 2) ^ 2 := by ring 
          _ = ((1 + Real.sqrt 5) / 2 : ℝ) * ((3 + Real.sqrt 5) / 2 : ℝ) := by rw [h1] 
          _ = (2 + Real.sqrt 5 : ℝ) := by 
            field_simp 
            ring_nf 
            <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
      have hx3 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 = (7 + 3 * Real.sqrt 5) / 2 := by 
        have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (3 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
        calc 
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 
            = (((1 + Real.sqrt 5) / 2 : ℝ) ^ 2) ^ 2 := by ring 
          _ = ((3 + Real.sqrt 5) / 2 : ℝ) ^ 2 := by rw [h1] 
          _ = (7 + 3 * Real.sqrt 5) / 2 := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
      have hx4 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 = 9 + 4 * Real.sqrt 5 := by 
        have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 = 2 + Real.sqrt 5 := by 
          have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (3 + Real.sqrt 5) / 2 := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
          calc 
            ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 
              = ((1 + Real.sqrt 5) / 2 : ℝ) * ((1 + Real.sqrt 5) / 2) ^ 2 := by ring 
            _ = ((1 + Real.sqrt 5) / 2 : ℝ) * ((3 + Real.sqrt 5) / 2 : ℝ) := by rw [h1] 
            _ = (2 + Real.sqrt 5 : ℝ) := by 
              field_simp 
              ring_nf 
              <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
        calc 
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 
            = (((1 + Real.sqrt 5) / 2 : ℝ) ^ 3) ^ 2 := by ring 
          _ = (2 + Real.sqrt 5 : ℝ) ^ 2 := by rw [h1] 
          _ = (9 + 4 * Real.sqrt 5 : ℝ) := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] 
      have num_eq : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 - ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = 2 + Real.sqrt 5 := by 
        rw [hx3, hx1] 
        nlinarith 
      have denom_eq : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 + 2 * ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 - 1 = 12 + 6 * Real.sqrt 5 := by 
        rw [hx4, hx2] 
        nlinarith 
      rw [num_eq, denom_eq] 
      have h5 : (2 + Real.sqrt 5 : ℝ) / (12 + 6 * Real.sqrt 5 : ℝ) = 1 / 6 := by 
        have h6 : (12 + 6 * Real.sqrt 5 : ℝ) = 6 * (2 + Real.sqrt 5 : ℝ) := by 
          ring 
        rw [h6] 
        field_simp 
        <;> nlinarith 
      linarith [h5] 
  -- Prove the value is the greatest 
  · -- Show that for any value in the set, it does not exceed 1/6 
    intro a ha 
    rcases ha with ⟨x, hx1, heq⟩ 
    have h1 : (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1) ≤ 1 / 6 := by 
      have pos1 : x ^ 6 + 2 * x ^ 3 - 1 > 0 := by 
        nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 3 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 1)]
      have h2 : 6 * (x ^ 4 - x ^ 2) - (x ^ 6 + 2 * x ^ 3 - 1) ≤ 0 := by 
        nlinarith [sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + x - 1), sq_nonneg (x ^ 2 - x - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 1)]
      have h3 : (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1) ≤ 1 / 6 := by 
        apply (div_le_div_iff (by positivity) (by positivity)).mpr 
        nlinarith [h2, pos1] 
      linarith 
    rw [heq] 
    linarith [h1]