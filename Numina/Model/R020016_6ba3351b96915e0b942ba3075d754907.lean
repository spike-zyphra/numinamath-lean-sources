import Mathlib

open Real

theorem algebra_37644 {x : ℚ} (hx : sqrt (x ^ 2 + 5) - x = 1 / 3) :
    x.num + x.den = 25 := by 
  have h1 : sqrt (x ^ 2 + 5) = x + 1 / 3 := by 
    have h : sqrt (x ^ 2 + 5) = x + 1 / 3 := by
      have h_eq : sqrt (x ^ 2 + 5) - x = (1 / 3 : ℝ) := by
        exact_mod_cast hx
      linarith
    exact h

  have h5 : x + 1/3 ≥ (0 : ℚ) := by
    have h4 : (x + 1/3 : ℝ) ≥ 0 := by
      have h3 : sqrt (x ^ 2 + 5) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 5)
      have h_eq : sqrt (x ^ 2 + 5) = (x + 1/3 : ℝ) := by
        linarith [h1]
      nlinarith
    have h7 : (↑x + (1/3 : ℝ) : ℝ) ≥ (0 : ℝ) := h4
    have h10 : (↑x + (1/3 : ℝ) : ℝ) = ↑(x + 1/3 : ℚ) := by
      simp
    have h9 : (↑(x + 1/3 : ℚ) : ℝ) ≥ (0 : ℝ) := by
      rw [h10] at h7
      linarith
    have h12 : (x + 1/3 : ℚ) ≥ (0 : ℚ) := by
      exact_mod_cast h9
    exact_mod_cast h12

  -- Next, we'll square both sides.

  -- $\sqrt{x^2 + 5}$ squared is $x^2 + 5$.
  -- $(x + \frac{1}{3})$ squared is $x^2 + \frac{2}{3} x + \frac{1}{9}$. 
  -- So we get $x^2 + 5 = x^2 + \frac{2}{3} x + \frac{1}{9}$

  have h3 : sqrt (x ^ 2 + 5) ^ 2 = (x + 1/3) ^ 2 := by 
    rw [h1]

  have h4 : sqrt (x ^ 2 + 5) ^ 2 = (x ^ 2 + 5 : ℝ) := by
    rw [Real.sq_sqrt]
    have : (x ^ 2 + 5 : ℝ) ≥ 0 := by
      have h7 : (x ^ 2 : ℝ) ≥ 0 := by
        exact sq_nonneg (x : ℝ)
      linarith
    linarith

  have h5 : (x + 1/3 : ℝ) ^ 2 = (x^2 + (2/3) * x + 1/9 : ℝ) := by 
    ring

  have h6 : (x^2 + 5 : ℝ) = (x^2 + (2/3) * x + 1/9 : ℝ) := by
    have h3' : sqrt (x ^ 2 + 5) ^ 2 = (x + 1/3 : ℝ) ^ 2 := h3
    nlinarith [h4, h5, h3']

  -- Subtract $x^2$ from both sides: $5 = \frac{2}{3} x + \frac{1}{9}$

  have h7 : (5 : ℝ) = (2/3) * (x : ℝ) + 1/9 := by
    nlinarith

  have h8 : (x : ℝ) = (22/3 : ℝ) := by
    nlinarith

  -- Now we need to show $x$ in `ℚ` equal to `22/3`.
  have h3' : (x : ℚ) = (22/3 : ℚ) := by
    have h10 : (↑x : ℝ) = (22/3 : ℝ) := by
      exact_mod_cast h8
    have h11 : (↑x : ℝ) = (↑(22/3 : ℚ) : ℝ) := by
      rw [h10]
      all_goals
        norm_num
    have h12 : x = (22/3 : ℚ) := by
      exact_mod_cast h11
    exact h12

  rw [h3']
  norm_num