import Mathlib

theorem algebra_311936 {x : ℝ} (hx : x ≠ 1 ∧ x ≠ -1) :
    (x / (x - 1))^2 + (x / (x + 1))^2 = 40 / 9 ↔
    x = 2 ∨ x = -2 ∨ x = Real.sqrt 55 / 11 ∨ x = -Real.sqrt 55 / 11 := by
  constructor
  · -- Assume the equation holds, prove the four possible solutions
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : x - 1 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : x + 1 ≠ 0 := by
      intro h3
      apply hx2
      linarith
    field_simp [(show x - 1 ≠ 0 by exact h1), (show x + 1 ≠ 0 by exact h2)] at h
    have h4 : (x - 2) * (x + 2) * (x^2 - 5 / 11) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show x - 1 ≠ 0 by exact h1), sq_pos_of_ne_zero (show x + 1 ≠ 0 by exact h2), sq_nonneg (x^2 - 4), sq_nonneg (x^2 - 5 / 11)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case $x - 2 = 0$, so $x = 2$.
      left
      linarith
    · -- Case $x + 2 = 0$, so $x = -2$.
      right
      left
      linarith
    · -- Case $x^2 - 5 / 11 = 0$
      have h9 : x^2 = 5 / 11 := by linarith
      have h10 : x = Real.sqrt 55 / 11 ∨ x = -Real.sqrt 55 / 11 := by
        have h100 : x^2 - (5 / 11) = 0 := by linarith
        have h101 : x^2 - (5 / 11) = (x - Real.sqrt 55 / 11) * (x + Real.sqrt 55 / 11) := by
          nlinarith [Real.sqrt_pos.mpr (show (55 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (55 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 55 / 11), sq_nonneg (x + Real.sqrt 55 / 11)]
        rw [h101] at h100
        cases' (mul_eq_zero.mp h100) with h102 h103
        · -- Case $x - \sqrt{55}/11 = 0$
          left
          linarith
        · -- Case $x + \sqrt{55}/11 = 0$
          right
          linarith
      cases' h10 with h11 h12
      · -- Case $x = \sqrt{55}/11$
        right
        right
        left
        exact h11
      · -- Case $x = -\sqrt{55}/11$
        right
        right
        right
        exact h12
  · -- Assume x is one of the four possible solutions, prove the equation holds
    rintro (h | h | h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = -2
      rw [h]
      norm_num
    · -- Case x = Real.sqrt 55 / 11
      rw [h]
      have h1 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (show 0 ≤ (55 : ℝ) by norm_num)
      field_simp [(show (Real.sqrt 55 : ℝ) - 11 ≠ 0 by
        by_contra h2
        have : Real.sqrt 55 = 11 := by nlinarith
        have h3 : Real.sqrt 55 ^ 2 = 11 ^ 2 := by rw [this]
        nlinarith [Real.sqrt_nonneg 55]
      ), (show (Real.sqrt 55 : ℝ) + 11 ≠ 0 by
        by_contra h2
        have : Real.sqrt 55 = -11 := by nlinarith
        have h3 : Real.sqrt 55 ^ 2 = (-11) ^ 2 := by rw [this]
        nlinarith [Real.sqrt_nonneg 55]
      )
      ]
      <;> nlinarith [h1, Real.sqrt_nonneg 55]
    · -- Case x = -Real.sqrt 55 / 11
      rw [h]
      have h1 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (show 0 ≤ (55 : ℝ) by norm_num)
      field_simp [(show (-Real.sqrt 55 : ℝ) - 11 ≠ 0 by
        by_contra h2
        have : Real.sqrt 55 = -11 - 0 := by
          nlinarith
        nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show (0 : ℝ) ≤ (55 : ℝ) by norm_num)]
      ), (show (-Real.sqrt 55 : ℝ) + 11 ≠ 0 by
        by_contra h2
        have : Real.sqrt 55 = 11 - 0 := by
          nlinarith
        nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show (0 : ℝ) ≤ (55 : ℝ) by norm_num)]
      )
      ]
      <;> nlinarith [h1, Real.sqrt_nonneg 55]