import Mathlib


open Real

theorem Algebra_611014 {x : ℝ} (hx : |x| < 1) (h : x = ∑' (i : ℕ), (-x) ^ i) :
  x = (-1 + sqrt 5)/ (2: ℝ) := by
  have h1 : ∑' (i : ℕ), (-x) ^ i = 1 / (1 + x) := by
    rw [tsum_geometric_of_norm_lt_one]
    · field_simp [(show 1 + x ≠ 0 by
        by_contra h'
        have : x = -1 := by linarith
        have : |x| = 1 := by
          rw [this]
          norm_num
        linarith [hx]
      )
    ]
    · -- Show that |-x| < 1
      have h2 : |(-x : ℝ)| < 1 := by
        have h3 : |(-x : ℝ)| = |x| := by
          simp [abs_neg]
        linarith [h3, hx]
      simpa using h2
  rw [h1] at h
  have h2 : x * (1 + x) = 1 := by
    field_simp [(show 1 + x ≠ 0 by
      by_contra h'
      have : x = -1 := by linarith
      have : |x| = 1 := by
        rw [this]
        norm_num
      linarith [hx]
    )] at h ⊢
    linarith
  have h3 : x ^ 2 + x - 1 = 0 := by
    nlinarith
  have h4 : x = (-1 + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 := by
    have h5 : x ^ 2 + x - 1 = 0 := h3
    have h6 : x ^ 2 + x - 1 = (x - (-1 + Real.sqrt 5) / 2) * (x - (-1 - Real.sqrt 5) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h6] at h5
    cases (mul_eq_zero.1 h5) with
    | inl h7 =>
      left
      linarith
    | inr h8 =>
      right
      linarith
  cases h4 with
  | inl h5 =>
    linarith
  | inr h6 =>
    -- Show that |-1 - sqrt 5| / 2 >= 1
    have h5 : x < -1 := by
      nlinarith [show Real.sqrt 5 > 0 by positivity, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h5' : |x| ≥ 1 := by
      have h6 : x < -1 := h5
      have h7 : |x| = -x := by
        rw [abs_of_nonpos (by linarith)]
        <;> nlinarith
      have h8 : |x| ≥ 1 := by
        have h9 : -x ≥ 1 := by nlinarith
        have h10 : |x| = -x := h7
        linarith
      linarith
    linarith [abs_lt.mp hx, h5']