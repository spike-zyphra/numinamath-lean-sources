import Mathlib

theorem algebra_234452 {x : ℝ} (hx : x > 0) :
    (Real.sqrt x - 1 / Real.sqrt x) * ((Real.sqrt x + 1) / (Real.sqrt x - 1) + 4 * x - (Real.sqrt x - 1) / (Real.sqrt x + 1)) = 112 - 4 * Real.sqrt x ↔ x = 9 := by
  constructor
  · -- Forward implication: if the equation holds, then x = 9
    intro h
    have h1 : Real.sqrt x > 0 := by
      positivity
    have h2 : Real.sqrt x ≠ 1 := by
      by_contra h3
      have h4 : Real.sqrt x = 1 := by linarith
      have h5 : x = 1 := by
        calc
          x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 1 ^ 2 := by rw [h4]
          _ = (1 : ℝ) := by norm_num
      rw [h4] at h
      norm_num [h5] at h <;> nlinarith [Real.sqrt_nonneg x]
    have h3 : Real.sqrt x - 1 ≠ 0 := by
      intro h4
      have h5 : Real.sqrt x = 1 := by linarith
      have h6 : Real.sqrt x ≠ 1 := h2
      contradiction
    have h4 : Real.sqrt x + 1 ≠ 0 := by 
      positivity
    have eq1 : (Real.sqrt x - 1 / Real.sqrt x) * ((Real.sqrt x + 1) / (Real.sqrt x - 1) + 4 * x - (Real.sqrt x - 1) / (Real.sqrt x + 1)) =
        4 + (4 * x * (x - 1) / Real.sqrt x) := by
      have h5 : Real.sqrt x > 0 := h1
      have h6 : Real.sqrt x - 1 ≠ 0 := h3
      have h7 : Real.sqrt x + 1 ≠ 0 := h4
      have eq2 : Real.sqrt x - 1 / Real.sqrt x = (x - 1) / Real.sqrt x := by
        field_simp [h5]
        <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
      have eq3 : (Real.sqrt x + 1) / (Real.sqrt x - 1) + 4 * x - (Real.sqrt x - 1) / (Real.sqrt x + 1) =
          (4 * Real.sqrt x) / (x - 1) + 4 * x := by
        have h8 : Real.sqrt x - 1 ≠ 0 := h3
        have h9 : Real.sqrt x + 1 ≠ 0 := h4
        field_simp [h8, h9, show x - 1 ≠ 0 by
          by_contra h10
          have h11 : x = 1 := by linarith
          have h12 : Real.sqrt x = 1 := by
            rw [h11]
            norm_num [Real.sqrt_eq_iff_sq_eq]
          have h13 : Real.sqrt x - 1 = 0 := by linarith
          contradiction
          ]
        <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
      rw [eq2]
      have eq4 : ((x - 1) / Real.sqrt x) * ((4 * Real.sqrt x) / (x - 1) + 4 * x) = 4 + (4 * x * (x - 1) / Real.sqrt x) := by
        field_simp [(show x - 1 ≠ 0 by
          by_contra h10
          have h11 : x = 1 := by linarith
          have h12 : Real.sqrt x = 1 := by
            rw [h11]
            norm_num [Real.sqrt_eq_iff_sq_eq]
          have h13 : Real.sqrt x - 1 = 0 := by linarith
          contradiction
          ), h5]
        <;> ring_nf <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
      rw [eq3]
      rw [eq4]
    rw [eq1] at h
    have h5 : 4 * x * (x - 1) / Real.sqrt x = 108 - 4 * Real.sqrt x := by
      nlinarith
    have h6 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by positivity)
    have h7 : x^2 = 27 * Real.sqrt x := by
      have h8 : Real.sqrt x ≥ 0 := by positivity
      have h9 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by positivity)
      have h10 : 4 * x * (x - 1) = 108 * Real.sqrt x - 4 * x := by
        have h11 : Real.sqrt x ≠ 0 := by positivity
        field_simp [h11] at h5
        nlinarith
      nlinarith [sq_nonneg (x - 9), sq_nonneg (Real.sqrt x - 3), Real.sq_sqrt (show 0 ≤ x by positivity)]
    have h9 : (Real.sqrt x) ^ 3 = 27 := by 
      nlinarith [Real.sq_sqrt (show 0 ≤ x by positivity), h7]
    have h10 : Real.sqrt x = 3 := by
      have h11 : (Real.sqrt x) ^ 3 - 27 = 0 := by nlinarith
      have h12 : (Real.sqrt x - 3) * ((Real.sqrt x) ^ 2 + (3:ℝ) * Real.sqrt x + 9) = 0 := by
        nlinarith [h11]
      cases' (mul_eq_zero.mp h12) with h13 h14
      · 
        linarith
      · 
        have h15 : (Real.sqrt x) ^ 2 + (3:ℝ) * Real.sqrt x + 9 > 0 := by
          nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x)]
        nlinarith
    have h11 : x = 9 := by
      calc
        x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (3) ^ 2 := by rw [h10]
        _ = (9 : ℝ) := by norm_num
    assumption
  · -- Reverse implication: if x = 9, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt (9 : ℝ) = 3 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h1]
    norm_num
    <;> nlinarith