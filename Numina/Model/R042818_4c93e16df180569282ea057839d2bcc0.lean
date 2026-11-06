import Mathlib

theorem algebra_166367 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x^3 / y + x * y = 40) (h2 : y^3 / x + x * y = 10) :
    (x, y) = (4, 2) ∨ (x, y) = (-4, -2) := by
  have eq1 : x^3 + x * y^2 = 40 * y := by
    have h3 : x^3 / y + x * y = 40 := h1
    have h4 : y ≠ 0 := hy
    field_simp at h3 ⊢
    nlinarith
  have eq2 : y^3 + x^2 * y = 10 * x := by
    have h5 : y^3 / x + x * y = 10 := h2
    have h6 : x ≠ 0 := hx
    field_simp at h5 ⊢
    nlinarith
  have eq3 : x * (x^2 + y^2) = 40 * y := by
    nlinarith [eq1]
  have eq4 : y * (x^2 + y^2) = 10 * x := by
    nlinarith [eq2]
  have eq5 : x^2 = 4 * y^2 := by
    have eq6 : x * (x^2 + y^2) = 40 * y := eq3
    have eq7 : y * (x^2 + y^2) = 10 * x := eq4
    have h10 : x * (x^2 + y^2) * y = 40 * y^2 := by
      have eq11 : x * (x^2 + y^2) = 40 * y := eq3
      rw [eq11] at *
      all_goals nlinarith
    have h11 : y * (x^2 + y^2) * x = 10 * x^2 := by
      have eq12 : y * (x^2 + y^2) = 10 * x := eq4
      rw [eq12] at *
      all_goals nlinarith
    nlinarith [sq_nonneg (x * y), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, h10, h11]
  have eq10 : x = 2 * y ∨ x = -2 * y := by
    have h11 : (x - 2 * y) * (x + 2 * y) = 0 := by
      nlinarith [eq5
      ]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- x - 2 * y = 0
      left
      linarith
    · -- x + 2 * y = 0
      right
      linarith
  cases eq10 with
  | inl h11 =>
    have eq11 : x = 2 * y := h11
    rw [show x = 2 * y by linarith [eq11] ] at eq3
    have eq12 : 10 * y^3 - 40 * y = 0 := by
      ring_nf at eq3 ⊢
      nlinarith
    have eq13 : 10 * y^3 - 40 * y = 0 := eq12
    have eq14 : y * (y^2 - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq14) with hy1 hy2
    · -- y = 0 
      exfalso
      apply hy
      linarith
    · -- y^2 - 4 = 0
      have eq15 : y^2 = 4 := by
        nlinarith
      have hy2' : y = 2 ∨ y = -2 := by
        have h17 : y^2 = 4 := eq15
        have : y = 2 ∨ y = -2 := by
          have h : y^2 - 4 = 0 := by linarith
          have : (y - 2) * (y + 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp this) with h18 h19
          · -- y - 2 = 0
            left
            linarith
          · -- y + 2 = 0
            right
            linarith
        assumption
      cases hy2' with
      | inl hy22 =>
        have eq16 : x = 4 := by
          nlinarith [eq11, hy22
          ]
        left
        simp [eq16, hy22
        ]
      | inr hy22 =>
        have eq17 : x = -4 := by
          nlinarith [eq11, hy22
          ]
        right
        simp [eq17, hy22
        ]
  | inr h11 =>
    have eq11 : x = -2 * y := by
      linarith [h11
      ]
    rw [show x = -2 * y by linarith [eq11] ] at eq3
    have eq12 : -10 * y^3 - 40 * y = 0 := by
      ring_nf at eq3 ⊢
      nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y ^ 2)
      ]
    have eq13 : -10 * y^3 - 40 * y = 0 := eq12
    have eq14 : -10 * y * (y^2 + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq14) with hy1 hy2
    · -- -10 * y = 0, so y = 0
      have hy0 : y = 0 := by
        nlinarith
      contradiction
    · -- y^2 + 4 = 0
      have eq15 : y^2 + 4 = 0 := by
        nlinarith
      nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (y ^ 2), sq_nonneg (y ^ 2 + 4), sq_nonneg (y ^ 2 + 4)
      ]