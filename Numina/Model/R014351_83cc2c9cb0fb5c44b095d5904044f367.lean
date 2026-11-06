import Mathlib

theorem algebra_188304 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * Real.sqrt y + y * Real.sqrt x = 6) (h2 : x ^ 2 * y + y ^ 2 * x = 20) :
    (x, y) = (4, 1) ∨ (x, y) = (1, 4) := by
  have eq1 : Real.sqrt x ^ 2 * Real.sqrt y + Real.sqrt y ^ 2 * Real.sqrt x = 6 := by
    have h3 : 0 < Real.sqrt x := by positivity
    have h4 : 0 < Real.sqrt y := by positivity
    have h5 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h6 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
    -- Re-express h1 using sqrts
    have eq1' : x * Real.sqrt y + y * Real.sqrt x = Real.sqrt x ^ 2 * Real.sqrt y + Real.sqrt y ^ 2 * Real.sqrt x := by
      rw [h5, h6]
      <;> nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    rw [eq1'] at h1
    linarith

  have eq2 : (Real.sqrt x ^ 2) ^ 2 * (Real.sqrt y ^ 2) + (Real.sqrt y ^ 2) ^ 2 * (Real.sqrt x ^ 2) = 20 := by
    have h3 : 0 < Real.sqrt x := by positivity
    have h4 : 0 < Real.sqrt y := by positivity
    have h5 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h6 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
    -- Re-express h2 using sqrts
    have eq2' : x ^ 2 * y + y ^ 2 * x = (Real.sqrt x ^ 2) ^ 2 * (Real.sqrt y ^ 2) + (Real.sqrt y ^ 2) ^ 2 * (Real.sqrt x ^ 2) := by
      rw [h5, h6]
      <;> nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    rw [eq2'] at h2
    linarith
  -- Factor eq1
  have h3 : Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) = 6 := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x + Real.sqrt y), mul_pos (show 0 < Real.sqrt x by positivity) (show 0 < Real.sqrt y by positivity)]
  -- Factor eq2
  have eq3 : (Real.sqrt x * Real.sqrt y) ^ 2 * ((Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2) = 20 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
      sq_nonneg (Real.sqrt x ^ 2 - Real.sqrt y ^ 2), sq_nonneg (Real.sqrt x * Real.sqrt y), sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x + Real.sqrt y),
      mul_pos (show 0 < Real.sqrt x by positivity) (show 0 < Real.sqrt y by positivity)
    ]
  -- Solving the system of equations
  have h4 : Real.sqrt x * Real.sqrt y = 2 := by
    nlinarith [sq_nonneg (Real.sqrt x ^ 2 - Real.sqrt y ^ 2), sq_nonneg (Real.sqrt x * Real.sqrt y), sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x + Real.sqrt y), mul_pos (show 0 < Real.sqrt x by positivity) (show 0 < Real.sqrt y by positivity), Real.sqrt_pos.mpr (show 0 < x by linarith), Real.sqrt_pos.mpr (show 0 < y by linarith),
      Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
    ]
  have h5 : Real.sqrt x + Real.sqrt y = 3 := by
    have h4' : Real.sqrt x * Real.sqrt y = 2 := h4
    have h3' : Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) = 6 := h3
    -- Solving the system of equations to find the value of s
    have h6 : Real.sqrt x + Real.sqrt y = 3 := by
      rw [show Real.sqrt x * Real.sqrt y = 2 by linarith] at h3'
      nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_pos (show 0 < Real.sqrt x by positivity) (show 0 < Real.sqrt y by positivity)]
    exact h6
  -- Solving quadratic equation
  have h6 : (Real.sqrt x - 2) * (Real.sqrt x - 1) = 0 := by
    have h5' : Real.sqrt x + Real.sqrt y = 3 := h5
    have h4' : Real.sqrt x * Real.sqrt y = 2 := h4
    -- Solving quadratic equation
    have h7 : (Real.sqrt x - 2) * (Real.sqrt x - 1) = 0 := by
      -- Expanding (Real.sqrt x - 2)(Real.sqrt x - 1) = Real.sqrt x^2 - 3*Real.sqrt x + 2 = 0
      have h8 : Real.sqrt x ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith
      have h9 : Real.sqrt y ^ 2 = y := by
        rw [Real.sq_sqrt]
        linarith
      have h10 : Real.sqrt x ^ 2 = 3 * Real.sqrt x - 2 := by
        have h11 : Real.sqrt y = 3 - Real.sqrt x := by linarith
        rw [h11] at h4'
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt x), sq_nonneg (Real.sqrt y)]
      nlinarith [Real.sqrt_nonneg x]
    exact h7
  cases' (mul_eq_zero.mp h6) with h71 h72
  · -- Case √x = 2
    have h8 : Real.sqrt x = 2 := by linarith
    have h9 : x = 4 := by
      calc
        x = Real.sqrt x ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 2 ^ 2 := by
          rw [h8]
        _ = 4 := by norm_num
    have h10 : Real.sqrt y = 1 := by
      nlinarith [h4, Real.sqrt_nonneg y, h8]
    have h11 : y = 1 := by
      calc
        y = Real.sqrt y ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 1 ^ 2 := by
          rw [h10]
        _ = 1 := by norm_num
    left
    simp [h9, h11]
    all_goals linarith
  · -- Case √x = 1
    have h8 : Real.sqrt x = 1 := by linarith
    have h9 : x = 1 := by
      calc
        x = Real.sqrt x ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 1 ^ 2 := by
          rw [h8]
        _ = 1 := by norm_num
    have h10 : Real.sqrt y = 2 := by
      nlinarith [h4, Real.sqrt_nonneg y, h8]
    have h11 : y = 4 := by
      calc
        y = Real.sqrt y ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 2 ^ 2 := by
          rw [h10]
        _ = 4 := by norm_num
    right
    simp [h9, h11]
    all_goals linarith