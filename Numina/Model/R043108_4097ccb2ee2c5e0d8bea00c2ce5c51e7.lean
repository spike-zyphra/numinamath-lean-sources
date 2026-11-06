import Mathlib


open Real

theorem algebra_291119 {x y : ℝ} (hx : (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1)
    (hy : (x ^ 2 + y + 2) * (y ^ 2 + x + 2) = 8) :
    (x, y) = (1, -1) ∨ (x, y) = (-1, 1) := by

  have h1 : x - Real.sqrt (x ^ 2 + 1) < 0 := by
    have h2 : x < Real.sqrt (x ^ 2 + 1) := by
      by_cases h : x ≥ 0
      · -- x >= 0
        have h3 : x < Real.sqrt (x ^ 2 + 1) := by
          rw [Real.lt_sqrt] <;> (nlinarith [sq_nonneg x, sq_nonneg (x^2 + 1)])
        linarith
      · -- x < 0
        have h10 : Real.sqrt (x ^ 2 + 1) > Real.sqrt (x ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 + 1)]
          · nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 + 1)]
        have h11 : Real.sqrt (x ^ 2) = |x| := by
          rw [Real.sqrt_sq_eq_abs]
        have h12 : Real.sqrt (x ^ 2 + 1) > |x| := by
          linarith [h10, h11]
        cases' abs_cases x with h h <;> nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]

  have h2 : y - Real.sqrt (y ^ 2 + 1) < 0 := by
    have h3 : y < Real.sqrt (y ^ 2 + 1) := by
      by_cases h : y ≥ 0
      · -- y >= 0
        have h4 : y < Real.sqrt (y ^ 2 + 1) := by
          rw [Real.lt_sqrt] <;> (nlinarith [sq_nonneg y, sq_nonneg (y^2 + 1)])
        linarith
      · -- y < 0
        have h10 : Real.sqrt (y ^ 2 + 1) > Real.sqrt (y ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2 + 1)]
          · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2 + 1)]
        have h11 : Real.sqrt (y ^ 2) = |y| := by
          rw [Real.sqrt_sq_eq_abs]
        have h12 : Real.sqrt (y ^ 2 + 1) > |y| := by
          linarith [h10, h11]
        cases' abs_cases y with h h <;> nlinarith [Real.sqrt_nonneg (y ^ 2 + 1)]
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 1)]

  have h3 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := by
    have h4 : x + Real.sqrt (x ^ 2 + 1) = -1 / (x - Real.sqrt (x ^ 2 + 1)) := by
      field_simp [(show (x - Real.sqrt (x ^ 2 + 1)) ≠ 0 by
        by_contra h
        have : x - Real.sqrt (x ^ 2 + 1) ≥ 0 := by linarith [h]
        linarith [h1, this]
      )]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by nlinarith)]
    have h5 : y + Real.sqrt (y ^ 2 + 1) = -1 / (y - Real.sqrt (y ^ 2 + 1)) := by
      field_simp [(show (y - Real.sqrt (y ^ 2 + 1)) ≠ 0 by
        by_contra h
        have : y - Real.sqrt (y ^ 2 + 1) ≥ 0 := by linarith [h]
        linarith [h2, this]
      )]
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ y ^ 2 + 1 by nlinarith)]
    rw [h4, h5]
    field_simp [(show (x - Real.sqrt (x ^ 2 + 1)) ≠ 0 by
      by_contra h
      have : x - Real.sqrt (x ^ 2 + 1) ≥ 0 := by linarith [h]
      linarith [h1, this]
    ),
      (show (y - Real.sqrt (y ^ 2 + 1)) ≠ 0 by
        by_contra h
        have : y - Real.sqrt (y ^ 2 + 1) ≥ 0 := by linarith [h]
        linarith [h2, this]
      )
    ]
    nlinarith [hx]

  have h4 : x * Real.sqrt (y ^ 2 + 1) + y * Real.sqrt (x ^ 2 + 1) = 0 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1),
      Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith),
      sq_nonneg (Real.sqrt (x ^ 2 + 1) - Real.sqrt (y ^ 2 + 1)), sq_nonneg (x - y),
      sq_nonneg (x + y)]

  have h5 : x^2 = y^2 := by
    have h8 : (x * Real.sqrt (y ^ 2 + 1)) ^ 2 = (y * Real.sqrt (x ^ 2 + 1)) ^ 2 := by
      have h6 : x * Real.sqrt (y ^ 2 + 1) = - (y * Real.sqrt (x ^ 2 + 1)) := by linarith [h4]
      rw [h6]
      ring
    have h9 : (x * Real.sqrt (y ^ 2 + 1)) ^ 2 = x ^ 2 * (Real.sqrt (y ^ 2 + 1) ^ 2) := by
      ring
    have h10 : (y * Real.sqrt (x ^ 2 + 1)) ^ 2 = y ^ 2 * (Real.sqrt (x ^ 2 + 1) ^ 2) := by
      ring
    have h11 : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h12 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h9] at h8
    rw [h10] at h8
    rw [h11] at h8
    rw [h12] at h8
    nlinarith

  have h6 : y = x ∨ y = -x := by
    have h7 : y ^ 2 = x ^ 2 := by
      linarith [h5]
    have h8 : y = x ∨ y = -x := by
      have h10 : y ^ 2 - x ^ 2 = 0 := by
        nlinarith
      have h11 : (y - x) * (y + x) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h11) with h12 h13
      · left
        linarith
      · right
        linarith
    exact h8

  cases h6 with
  | inl h7 =>
    have h7' : x * Real.sqrt (y ^ 2 + 1) + y * Real.sqrt (x ^ 2 + 1) = 0 := h4
    rw [show y = x by linarith [h7]] at h7'
    have h8 : 2 * x * Real.sqrt (x ^ 2 + 1) = 0 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
    have h9 : x * Real.sqrt (x ^ 2 + 1) = 0 := by
      linarith
    have h10 : x = 0 := by
      have h11 : Real.sqrt (x ^ 2 + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      have h12 : x = 0 := by
        apply (mul_left_inj' (ne_of_gt h11)).mp
        linarith
      exact h12
    have h11 : y = 0 := by
      linarith [h10, show y = x by linarith [h7]]
    rw [show x = 0 by linarith [h10], show y = 0 by linarith [h11]] at hy
    norm_num at hy
  | inr h7 =>
    have h13 : y = -x := by
      linarith
    have h14 : (x ^ 2 + y + 2) * (y ^ 2 + x + 2) = 8 := by
      nlinarith [hy]
    rw [show y = -x by linarith [h13]] at h14
    have h15 : x ^ 4 + 3 * x ^ 2 - 4 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - x + 2), sq_nonneg (x ^ 2 - 1)]
    have h16 : x^2 = 1 := by
      have h17 : x^4 + 3 * x^2 - 4 = 0 := h15
      have h18 : (x^2 + 4) * (x^2 - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h18) with h19 h20
      · -- x ^ 2 + 4 = 0
        nlinarith [sq_nonneg x]
      · -- x ^ 2 - 1 = 0
        nlinarith
    have h17 : x = 1 ∨ x = -1 := by
      have h18 : x ^ 2 = 1 := h16
      have h19 : x = 1 ∨ x = -1 := by
        rw [sq_eq_one_iff] at h18
        tauto
      exact h19
    cases h17 with
    | inl h18 =>
      have h19 : x = 1 := h18
      have h20 : y = -1 := by
        nlinarith [show y = -x by linarith [h13], h19]
      left
      simp [h19, h20]
    | inr h18 =>
      have h19 : x = -1 := h18
      have h20 : y = 1 := by
        nlinarith [show y = -x by linarith [h13], h19]
      right
      simp [h19, h20]