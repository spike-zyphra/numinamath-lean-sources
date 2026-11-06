import Mathlib

open Real

theorem algebra_216897 {f g h : ℝ → ℝ}
    (hf : f = fun x => x^3 + 2 * x^2 + 3 * x + 1)
    (hg : g = fun x => x^4 - x^3 + 4 * x^2 + 8 * x + 8)
    (hh : h = fun x => x + 1) :
    ∀ x, f ⁻¹' {g x} = {h x} ↔ x = (3 + sqrt 5) / 2 ∨ x = (3 - sqrt 5) / 2 := by 
  intro x
  constructor
  · -- Assume f⁻¹{g(x)} = {h(x)}, prove x = (3 ± sqrt 5)/2
    intro h_eq
    have h2 : f (h x) = g x := by
      have hfx : h x ∈ f ⁻¹' {g x} := by
        rw [h_eq]
        simp
      simpa using hfx
    simp [hf, hg, hh] at h2
    have h_eq1 : (x + 1)^3 + 2*(x + 1)^2 + 3*(x + 1) + 1 = x^4 - x^3 + 4*x^2 + 8*x + 8 := by linarith
    have eq2 : x^4 - 2*x^3 - x^2 - 2*x + 1 = 0 := by
      nlinarith [h_eq1]
    have h4 : (x^2 - 3*x + 1) * (x^2 + x + 1) = 0 := by 
      nlinarith [eq2]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where x^2 - 3x + 1 = 0
      have h7 : x^2 - 3*x + 1 = 0 := h5
      have h8 : (x - (3 + Real.sqrt 5) / 2) * (x - (3 - Real.sqrt 5) / 2) = 0 := by
        have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
        nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case x = (3 + sqrt 5)/2
        left
        linarith
      · -- Case x = (3 - sqrt 5)/2
        right
        linarith
    · -- Case where x^2 + x + 1 = 0
      have h7 : x^2 + x + 1 = 0 := h6
      have h8 : x^2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0)]
      linarith
  · -- Assume x = (3 ± sqrt 5)/2, prove f⁻¹{g(x)} = {h(x)}
    rintro (h | h)
    · -- Case x = (3 + sqrt 5)/2
      ext y
      simp [hf, hg, hh, h]
      constructor
      · -- Forward implication: if f(y) = g(x), then y = h(x)
        intro f_eq
        have eq1 : (y^3 + 2*y^2 + 3*y + 1) - ((3 + Real.sqrt 5)/2 + 1)^3 - 2*((3 + Real.sqrt 5)/2 + 1)^2 - 3*((3 + Real.sqrt 5)/2 + 1) - 1 = 0 := by
          nlinarith [f_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        have eq2 : (y - ((3 + Real.sqrt 5)/2 + 1)) * ((y^2 + ((3 + Real.sqrt 5)/2 + 1)*y + ((3 + Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 + Real.sqrt 5)/2 + 1)) + 3) = 0 := by
          nlinarith [eq1, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        cases' (mul_eq_zero.mp eq2) with h1 h2
        · -- Case y - ((3 + sqrt 5)/2 + 1) = 0
          linarith
        · -- Case cubic = 0
          have h3 : (y^2 + ((3 + Real.sqrt 5)/2 + 1)*y + ((3 + Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 + Real.sqrt 5)/2 + 1)) + 3 ≠ 0 := by
            have h4 : (y^2 + ((3 + Real.sqrt 5)/2 + 1)*y + ((3 + Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 + Real.sqrt 5)/2 + 1)) + 3 > 0 := by
              nlinarith [sq_nonneg (y + ((3 + Real.sqrt 5)/2 + 1)), sq_nonneg (y + ((3 + Real.sqrt 5)/2 + 1) + 1), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
            linarith
          contradiction
      · -- Backward implication: if y = h(x), then f(y) = g(x)
        intro y_eq
        rw [y_eq]
        -- Check f(h(x)) = g(x)
        have g_eq : ((3 + Real.sqrt 5)/2)^4 - ((3 + Real.sqrt 5)/2)^3 + 4*((3 + Real.sqrt 5)/2)^2 + 8*((3 + Real.sqrt 5)/2) + 8 = ((3 + Real.sqrt 5)/2 + 1)^3 + 2*((3 + Real.sqrt 5)/2 + 1)^2 + 3*((3 + Real.sqrt 5)/2 + 1) + 1 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        nlinarith [g_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    · -- Case x = (3 - sqrt 5)/2
      ext y
      simp [hf, hg, hh, h]
      constructor
      · -- Forward implication: if f(y) = g(x), then y = h(x)
        intro f_eq
        have eq1 : (y^3 + 2*y^2 + 3*y + 1) - ((3 - Real.sqrt 5)/2 + 1)^3 - 2*((3 - Real.sqrt 5)/2 + 1)^2 - 3*((3 - Real.sqrt 5)/2 + 1) - 1 = 0 := by
          nlinarith [f_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        have eq2 : (y - ((3 - Real.sqrt 5)/2 + 1)) * ((y^2 + ((3 - Real.sqrt 5)/2 + 1)*y + ((3 - Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 - Real.sqrt 5)/2 + 1)) + 3) = 0 := by
          nlinarith [eq1, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        cases' (mul_eq_zero.mp eq2) with h1 h2
        · -- Case y - ((3 - sqrt 5)/2 + 1) = 0
          linarith
        · -- Case cubic = 0
          have h3 : (y^2 + ((3 - Real.sqrt 5)/2 + 1)*y + ((3 - Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 - Real.sqrt 5)/2 + 1)) + 3 ≠ 0 := by
            have h4 : (y^2 + ((3 - Real.sqrt 5)/2 + 1)*y + ((3 - Real.sqrt 5)/2 + 1)^2) + 2*(y + ((3 - Real.sqrt 5)/2 + 1)) + 3 > 0 := by
              nlinarith [sq_nonneg (y + ((3 - Real.sqrt 5)/2 + 1)), sq_nonneg (y + ((3 - Real.sqrt 5)/2 + 1) + 1), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
            linarith
          contradiction
      · -- Backward implication: if y = h(x), then f(y) = g(x)
        intro y_eq
        rw [y_eq]
        -- Check f(h(x)) = g(x)
        have g_eq : ((3 - Real.sqrt 5)/2)^4 - ((3 - Real.sqrt 5)/2)^3 + 4*((3 - Real.sqrt 5)/2)^2 + 8*((3 - Real.sqrt 5)/2) + 8 = ((3 - Real.sqrt 5)/2 + 1)^3 + 2*((3 - Real.sqrt 5)/2 + 1)^2 + 3*((3 - Real.sqrt 5)/2 + 1) + 1 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        nlinarith [g_eq, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]