import Mathlib
/-3. If the positive real numbers $x \backslash y$ satisfy $y=2016 x$, and $x^{y}=y^{x}$, then $\log _{2016} x+\log _{2016} y=$ $\qquad$-/
theorem algebra_325876 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : y = 2016 * x) (hxp : x ^ y = y ^ x) :
    Real.logb 2016 x + Real.logb 2016 y = 2017 / 2015 := by
  have h1 : y = 2016 * x := hxy
  have h2 : x ^ y = y ^ x := hxp
  rw [h1] at h2
  have h3 : x ≠ 0 := by linarith
  have h4 : Real.logb 2016 x + Real.logb 2016 y = 2017 / 2015 := by
    have eq1 : x ^ (2016 * x) = (2016 * x) ^ x := by
      exact h2
    have h5 : Real.logb 2016 x + Real.logb 2016 y = 2017 / 2015 := by
      have h6 : Real.log (x ^ (2016 * x)) = Real.log ((2016 * x) ^ x) := by
        rw [eq1]
      have h7 : Real.log (x ^ (2016 * x)) = 2016 * x * Real.log x := by
        have h_pos : x > 0 := hx
        have h8 : 2016 * x > 0 := by nlinarith
        rw [Real.log_rpow]
        all_goals linarith
      have h9 : Real.log ((2016 * x) ^ x) = x * Real.log (2016 * x) := by
        have h_pos : (2016 * x) > 0 := by nlinarith
        rw [Real.log_rpow]
        all_goals linarith
      have h10 : Real.log (2016 * x) = Real.log 2016 + Real.log x := by
        have h_pos1 : (2016 : ℝ) > 0 := by norm_num
        have h_pos2 : x > 0 := hx
        exact Real.log_mul (by linarith) (by linarith)
      rw [h7, h9, h10] at h6
      have h11 : x ≠ 0 := by linarith
      have h12 : Real.log x = Real.log 2016 / 2015 := by
        have h13 : x ≠ 0 := h11
        have h14 : x > 0 := hx
        have h15 : Real.log x = Real.log 2016 / 2015 := by
          have h16 : 2016 * x * Real.log x = x * (Real.log 2016 + Real.log x) := by linarith
          have h17 : x ≠ 0 := h13
          have h18 : x > 0 := h14
          have h19 : Real.log x = Real.log 2016 / 2015 := by
            have h20 : 2015 * Real.log x = Real.log 2016 := by
              nlinarith [h16]
            have h21 : Real.log x = Real.log 2016 / 2015 := by
              linarith
            exact h21
          exact h19
        exact h15
      have h13 : Real.logb 2016 x = 1 / 2015 := by
        have h14 : Real.logb 2016 x = Real.log x / Real.log 2016 := by
          field_simp [Real.logb]
        rw [h14]
        have h15 : Real.log x = Real.log 2016 / 2015 := by
          exact h12
        have h16 : Real.log 2016 ≠ 0 := by
          have h17 : (2016 : ℝ) > 1 := by norm_num
          have h18 : Real.log 2016 > 0 := by
            apply Real.log_pos
            linarith
          linarith
        have h17 : Real.log x = Real.log 2016 / 2015 := by
          exact h15
        field_simp [h16]
        linarith
      have h14 : Real.logb 2016 y = 2016 / 2015 := by
        have h15 : y = 2016 * x := h1
        rw [h15]
        have h16 : Real.logb 2016 (2016 * x) = Real.logb 2016 2016 + Real.logb 2016 x := by
          have h17 : (2016 : ℝ) > 0 := by norm_num
          have h18 : x > 0 := hx
          have h19 : (2016 : ℝ) ≠ 1 := by norm_num
          have h20 : Real.logb 2016 (2016 * x) = Real.logb 2016 2016 + Real.logb 2016 x := by
            rw [Real.logb_mul (by linarith) (by linarith)]
          exact h20
        rw [h16]
        have h17 : Real.logb 2016 (2016 : ℝ) = 1 := by
          rw [Real.logb_self_eq_one]
          all_goals linarith
        rw [h17]
        have h18 : Real.logb 2016 x = 1 / 2015 := h13
        linarith
      linarith [h13, h14]
    exact h5
  exact h4