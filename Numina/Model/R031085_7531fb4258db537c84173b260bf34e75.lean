import Mathlib

theorem algebra_128667 {a b c : ℝ} (ha : a ≠ b) (hc : c > 0)
    (h1 : a^4 - 2019 * a = c) (h2 : b^4 - 2019 * b = c) :
    -Real.sqrt c < a * b ∧ a * b < 0 := by

  have h3 : a^4 - 2019 * a - (b^4 - 2019 * b) = 0 := by
    linarith [h1, h2]

  have h4 : (a - b) * ((a + b) * (a^2 + b^2) - 2019) = 0 := by
    ring_nf at h3 ⊢
    nlinarith

  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- h5
    have h7 : a = b := by linarith
    contradiction
  · -- h6
    have h8 : (a + b) * (a^2 + b^2) = 2019 := by linarith

    have h9 : a * b < 0 := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg ((a + b) * (a - b)), sq_nonneg ((a ^ 2 + b ^ 2) * (a - b)), sq_nonneg (a * b), sq_nonneg (a * (a * b)), sq_nonneg (b * (a * b)), sq_pos_of_pos hc, sq_nonneg ((a + b) * (a^2 + b^2))]

    have h9' : -Real.sqrt c < a * b := by
      have h11 : (a * b) ^ 2 < c := by
        nlinarith [sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg ((a + b) * (a ^ 2 + b ^ 2)), sq_nonneg ((a - b) * (a * b)), sq_nonneg (a * b), sq_nonneg ((a^4 - b^4)), sq_nonneg ((a^2 - b^2) * (a^2 + b^2)), sq_nonneg ((a + b) * (a - b)), sq_nonneg ((a^2 + b^2) * (a - b)), sq_nonneg (a * b), sq_nonneg (a * (a * b)), sq_nonneg (b * (a * b))]
      have h12 : Real.sqrt c > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h13 : Real.sqrt (c) ^ 2 = c := Real.sq_sqrt (by linarith)
      have h14 : (a * b) ^ 2 < (Real.sqrt c) ^ 2 := by linarith [h11, h13]
      have h15 : (a * b) + Real.sqrt c > 0 := by
        nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by linarith), sq_nonneg ((a * b) - Real.sqrt c), sq_nonneg (a * b), sq_nonneg (Real.sqrt c)]
      nlinarith [Real.sqrt_nonneg c]

    constructor
    · -- Show -Real.sqrt c < a * b
      linarith [h9']
    · -- Show a * b < 0
      linarith [h9]