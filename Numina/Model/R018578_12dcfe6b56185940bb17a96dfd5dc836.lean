import Mathlib

theorem algebra_187338 {x y : ℝ} (h₀ : x ≥ 0) (h₁ : y ≥ 0)
    (h₂ : Real.sqrt x - Real.sqrt y = 0.5 * Real.sqrt (x * y)) (h₃ : x + y = 5) :
    x = 4 ∧ y = 1 := by

  have h4 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by 
    rw [Real.sqrt_mul (by linarith)]
  rw [h4] at h₂

  have h5 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
  have h6 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)

  have eq1 : (Real.sqrt x - Real.sqrt y) ^ 2 = (0.5 * (Real.sqrt x * Real.sqrt y)) ^ 2 := by 
    rw [h₂]

  have eq2 : (Real.sqrt x - Real.sqrt y) ^ 2 = (Real.sqrt x) ^ 2 - 2 * (Real.sqrt x * Real.sqrt y) + (Real.sqrt y) ^ 2 := by 
    ring

  have eq3 : (0.5 * (Real.sqrt x * Real.sqrt y)) ^ 2 = (0.5 : ℝ) ^ 2 * (Real.sqrt x * Real.sqrt y) ^ 2 := by 
    ring

  have eq4 : (Real.sqrt x * Real.sqrt y) ^ 2 = x * y := by 
    calc 
      (Real.sqrt x * Real.sqrt y) ^ 2 = (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 := by ring
      _ = x * y := by 
        rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  -- Now, expanding and substituting the squares.

  -- From Equation (1): (Real.sqrt x - Real.sqrt y)^2 = (0.5 * Real.sqrt x * Real.sqrt y)^2.

  have eq5 : x - 2 * (Real.sqrt x * Real.sqrt y) + y = (0.5 : ℝ) ^ 2 * (x * y) := by 
    rw [eq2, eq3] at eq1
    rw [h5, h6] at eq1 
    linarith
  have eq6 : Real.sqrt x * Real.sqrt y = 2 := by
    have h₄ : x + y = 5 := h₃
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x * Real.sqrt y - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), sq_nonneg (Real.sqrt x ^ 2 - x), sq_nonneg (Real.sqrt y ^ 2 - y)
    ]
  -- Now from sqrt x * sqrt y = 2, we derive x * y =4.

  have eq7 : x * y = 4 := by 
    calc
      x * y = (Real.sqrt x * Real.sqrt y) ^ 2 := by rw [eq4]
      _ = 2 ^ 2 := by rw [eq6]
      _ = 4 := by norm_num
  
  -- Now we have for x and y, x+y=5 and x * y =4.
  -- This means solving the quadratic t^2 -5t +4 =0. the solutions are t=1 and t=4
  -- Therefore either [x=1, y=4] or [x=4, y=1]. We need to verify these in the original equation.

  -- This substitution should be done properly.
  
  -- Due to $x \cdot (5/x) =7.$

  -- But problem: two solutions, ring approach helps.

  -- Now we will have to use the first equation to verify. First substitution.
  -- For $x=1, y=4.$ This would lead to invalid equality as we saw earlier.

  have eq8 : x * y = 4 := eq7 
  have eq10 : y = 5 - x := by linarith 
  rw [eq10] at eq8 
  -- now the equation is x * (5 - x) =4.
  have h33 : x * (5 - x) = 4 := eq8 
  have eq9 : (x - 1) * (x - 4) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq9) with h4 h4
  · -- Case where x = 1
    -- This leads to a contradiction when substituted in the original equation.
    -- This approach is explicitly required
    have eq11 : x = 1 := by linarith 
    have eq12 : y = 4 := by linarith 
    -- Derive contradiction by substituting in Original Equation 
    -- The original equation and derived equal solutions.
    have eq13 : Real.sqrt x = 1 := by 
      rw [eq11]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    have eq14 : Real.sqrt y = 2 := by 
      rw [eq12]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    rw [eq13, eq14] at h₂ 
    norm_num at h₂ 
  · -- Case where x = 4
    -- This leads to the final answer
    have eq11 : x = 4 := by linarith 
    have eq12 : y = 1 := by linarith 
    constructor 
    · exact eq11 
    · exact eq12