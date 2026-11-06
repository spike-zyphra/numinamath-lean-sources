import Mathlib

theorem algebra_250522
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hne : b ≠ c)
    (h1 : Real.sqrt a + Real.sqrt b ≠ Real.sqrt c)
    (h2 : a + b = (Real.sqrt a + Real.sqrt b - Real.sqrt c)^2) :
    (a + (Real.sqrt a - Real.sqrt c)^2) / (b + (Real.sqrt b - Real.sqrt c)^2) =
    (Real.sqrt a - Real.sqrt c) / (Real.sqrt b - Real.sqrt c) := by
  have h3 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h4 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have h5 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have h6 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have h7 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have h8 : Real.sqrt c ^ 2 = c := Real.sq_sqrt (by linarith)
  have h9 : 2 * (Real.sqrt a * Real.sqrt c) + 2 * (Real.sqrt b * Real.sqrt c) - 2 * (Real.sqrt a * Real.sqrt b) - c = 0 := by
    nlinarith [h2, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]
  have h10 : Real.sqrt b - Real.sqrt c ≠ 0 := by
    intro h
    apply hne
    have : b = c := by
      have h3 : Real.sqrt b = Real.sqrt c := by linarith [h]
      have h4 : (Real.sqrt b) ^ 2 = (Real.sqrt c) ^ 2 := by
        rw [h3]
      nlinarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith)]
    linarith
  have h11 : b + (Real.sqrt b - Real.sqrt c)^2 ≠ 0 := by
    have hb1 : 0 ≤ b := hb
    have h12 : 0 ≤ (Real.sqrt b - Real.sqrt c)^2 := sq_nonneg (Real.sqrt b - Real.sqrt c)
    nlinarith [sq_pos_of_ne_zero (show Real.sqrt b - Real.sqrt c ≠ 0 by
      intro h
      apply hne
      have : b = c := by
        have h3 : Real.sqrt b = Real.sqrt c := by linarith [h]
        have h4 : (Real.sqrt b) ^ 2 = (Real.sqrt c) ^ 2 := by
          rw [h3]
        nlinarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith)]
      linarith
    ), Real.sqrt_nonneg b, Real.sqrt_nonneg c]
  have h12 : (a + (Real.sqrt a - Real.sqrt c)^2) * (Real.sqrt b - Real.sqrt c) = (b + (Real.sqrt b - Real.sqrt c)^2) * (Real.sqrt a - Real.sqrt c) := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (Real.sqrt b - Real.sqrt c), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), 
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, 
      h9
    ]
  have h13 : (a + (Real.sqrt a - Real.sqrt c)^2) / (b + (Real.sqrt b - Real.sqrt c)^2) = (Real.sqrt a - Real.sqrt c) / (Real.sqrt b - Real.sqrt c) := by
    have h14 : b + (Real.sqrt b - Real.sqrt c)^2 ≠ 0 := h11
    have h15 : Real.sqrt b - Real.sqrt c ≠ 0 := h10
    field_simp [h14, h15]
    <;> linarith [h12]
  exact h13