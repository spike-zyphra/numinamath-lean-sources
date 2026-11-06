import Mathlib

theorem algebra_132617 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ∃ d, b = a + d ∧ c = b + d) :
    ∃ x y, x ≠ y ∧ a * x ^ 2 + 2 * Real.sqrt 2 * b * x + c = 0 ∧
    a * y ^ 2 + 2 * Real.sqrt 2 * b * y + c = 0 := by 
  rcases h with ⟨d, h1, h2⟩

  have h3 : c = 2 * b - a := by
    nlinarith

  have h4 : (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c > 0 := by 
    rw [h3]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_pos_of_ne_zero hb, sq_pos_of_ne_zero ha, sq_nonneg (b - a), sq_nonneg (d)]

  use (-2 * Real.sqrt 2 * b + Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a),
    (-2 * Real.sqrt 2 * b - Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)

  constructor
  · -- Show x ≠ y
    by_contra h_eq
    have h6 : (-2 * Real.sqrt 2 * b + Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a) =
      (-2 * Real.sqrt 2 * b - Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a) := by
      linarith [h_eq]
    have h7 : -2 * Real.sqrt 2 * b + Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) =
        -2 * Real.sqrt 2 * b - Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) := by
      field_simp [ha] at h6
      <;> linarith [h6]
    have h8 : Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) = 0 := by 
      nlinarith
    have h9 : (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c > 0 := h4
    have h10 : Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith
    nlinarith
  constructor
  · -- Show a * x ^ 2 + 2 * Real.sqrt 2 * b * x + c = 0
    have eq1 : a * ((-2 * Real.sqrt 2 * b + Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) ^ 2 + 2 * Real.sqrt 2 * b * ((-2 * Real.sqrt 2 * b + Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) + c = 0 := by
      have h5 : a ≠ 0 := ha
      have h6 : (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c ≥ 0 := by nlinarith
      have hx1 : Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) ≥ 0 := by apply Real.sqrt_nonneg
      have h7 : (Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) ^ 2 = (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c := by 
        rw [Real.sq_sqrt]
        nlinarith
      field_simp
      <;> nlinarith [h6, h7, Real.sqrt_nonneg ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c by nlinarith)]
    simpa using eq1
  · -- Show a * y ^ 2 + 2 * Real.sqrt 2 * b * y + c = 0
    have eq2 : a * ((-2 * Real.sqrt 2 * b - Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) ^ 2 + 2 * Real.sqrt 2 * b * ((-2 * Real.sqrt 2 * b - Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) + c = 0 := by
      have h5 : a ≠ 0 := ha
      have h6 : (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c ≥ 0 := by nlinarith
      have hx1 : Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c) ≥ 0 := by apply Real.sqrt_nonneg
      have h7 : (Real.sqrt ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c)) ^ 2 = (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c := by 
        rw [Real.sq_sqrt]
        nlinarith
      field_simp
      <;> nlinarith [h6, h7, Real.sqrt_nonneg ((2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c by nlinarith)]
    simpa using eq2