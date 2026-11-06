import Mathlib

theorem algebra_259865 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + b^2 = 1) (X Y Z : ℝ)
    (hX : X = (a^4 + b^4) / (a^6 + b^6))
    (hY : Y = (a^4 + b^4) / Real.sqrt (a^6 + b^6))
    (hZ : Z = Real.sqrt (a^4 + b^4) / (a^6 + b^6)) :
    Y < X ∧ X < Z := by

  have h1 : 0 < a^2 * b^2 := by
    have ha2 : 0 < a^2 := by
      apply sq_pos_of_ne_zero 
      exact ha
    have hb2 : 0 < b^2 := by
      apply sq_pos_of_ne_zero 
      exact hb
    nlinarith [mul_pos ha2 hb2]

  have h2 : a^4 + b^4 = (1 : ℝ) - 2 * (a^2 * b^2) := by
    have h11 : a^4 + b^4 = (a^2 + b^2)^2 - 2 * (a^2 * b^2) := by 
      nlinarith
    rw [h] at h11
    linarith

  have h3 : a^6 + b^6 = (1 : ℝ) - 3 * (a^2 * b^2) := by
    have h44 : a^6 + b^6 = (a^2 + b^2)^3 - 3 * (a^2 * b^2) * (a^2 + b^2) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]
    rw [h] at h44
    nlinarith

  have h4 : 0 < a^6 + b^6 := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_pos_of_pos (show 0 < a^2 by positivity), sq_pos_of_pos (show 0 < b^2 by positivity)]

  have h5 : a^6 + b^6 < (1 : ℝ) := by
    nlinarith [sq_pos_of_pos (show 0 < a^2 by positivity), sq_pos_of_pos (show 0 < b^2 by positivity), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]

  have h11 : 0 < Real.sqrt (a^6 + b^6) := by
    apply Real.sqrt_pos.mpr
    linarith

  have h14 : Real.sqrt (a^6 + b^6) < (1 : ℝ) := by
    have h9 : a^6 + b^6 < (1 : ℝ) := h5
    have h10 : Real.sqrt (a^6 + b^6) < Real.sqrt ((1 : ℝ) : ℝ) := by
      apply Real.sqrt_lt_sqrt
      all_goals linarith
    have h111 : Real.sqrt ((1 : ℝ) : ℝ) = (1 : ℝ) := by 
      rw [Real.sqrt_one]
    linarith [h111, h10]

  have h10 : 0 < a^4 + b^4 := by
    nlinarith [sq_pos_of_pos (show 0 < a^2 by positivity), sq_pos_of_pos (show 0 < b^2 by positivity), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]

  have h18 : Y < X := by
    rw [hY, hX]
    have h19 : 0 < a^4 + b^4 := h10
    have h15 : Real.sqrt (a^6 + b^6) > a^6 + b^6 := by
      nlinarith [h4, h5, h11, Real.sqrt_nonneg (a^6 + b^6), Real.sq_sqrt (show 0 ≤ (a ^ 6 + b ^ 6 : ℝ) by positivity)]
    have h16 : (a^4 + b^4) / Real.sqrt (a^6 + b^6) < (a^4 + b^4) / (a^6 + b^6) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h15, h19]
    linarith

  have h22 : X < Z := by
    rw [hX, hZ]
    have h15 : 0 < a^6 + b^6 := h4
    have h100 : a^4 + b^4 < Real.sqrt (a^4 + b^4) := by
      have h66 : a^4 + b^4 < (1 : ℝ) := by
        have h111 : a^4 + b^4 = 1 - 2 * (a^2 * b^2) := h2
        have h222 : 0 < a^2 * b^2 := h1
        nlinarith
      have h111 : Real.sqrt (a^4 + b^4) > a^4 + b^4 := by
        have h10 : (a^4 + b^4) < (1 : ℝ) := h66
        nlinarith [Real.sqrt_nonneg (a^4 + b^4), Real.sq_sqrt (show 0 ≤ (a ^ 4 + b ^ 4 : ℝ) by positivity), sq_nonneg (Real.sqrt (a^4 + b^4) - (a^4 + b^4))]
      linarith
    have h16 : (a^4 + b^4) / (a^6 + b^6) < Real.sqrt (a^4 + b^4) / (a^6 + b^6) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h100]
    linarith

  constructor
  · exact h18
  · exact h22