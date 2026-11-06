import Mathlib

theorem algebra_296513 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h₀ : a + b + c + d = 4) (h₁ : a^2 + b^2 + c^2 + d^2 = 8) :
    max (max a b) (max c d) ≤ 1 + Real.sqrt 3 := by

  have h8 : a ≤ 1 + Real.sqrt 3 := by
    have h2 : (b + c + d)^2 ≤ 3 * (b^2 + c^2 + d^2) := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h3 : (b + c + d) = 4 - a := by
      linarith 
    have h4 : (b^2 + c^2 + d^2) = 8 - a^2 := by
      nlinarith
    rw [h3, h4] at h2 
    have h5 : (4 - a)^2 ≤ 3 * (8 - a^2) := by
      nlinarith 
    have h7 : a^2 - 2 * a - 2 ≤ 0 := by
      nlinarith
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

  have h12 : b ≤ 1 + Real.sqrt 3 := by
    have h2' : (a + c + d)^2 ≤ 3 * (a^2 + c^2 + d^2) := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (c - d)]
    have h3' : (a + c + d) = 4 - b := by
      linarith 
    have h4' : (a^2 + c^2 + d^2) = 8 - b^2 := by
      nlinarith
    rw [h3', h4'] at h2'
    have h6 : (4 - b)^2 - 3 * (8 - b^2) ≤ 0 := by
      nlinarith 
    have h7 : b ^ 2 - 2 * b - 2 ≤ 0 := by
      nlinarith
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

  have h13 : c ≤ 1 + Real.sqrt 3 := by
    have h2' : (a + b + d)^2 ≤ 3 * (a^2 + b^2 + d^2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (b - d)]
    have h3' : (a + b + d) = 4 - c := by
      linarith 
    have h4' : (a^2 + b^2 + d^2) = 8 - c^2 := by
      nlinarith
    rw [h3', h4'] at h2'
    have h6 : (4 - c)^2 - 3 * (8 - c^2) ≤ 0 := by
      nlinarith 
    have h7 : c ^ 2 - 2 * c - 2 ≤ 0 := by
      nlinarith
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

  have h14 : d ≤ 1 + Real.sqrt 3 := by
    have h2' : (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h3' : (a + b + c) = 4 - d := by
      linarith 
    have h4' : (a^2 + b^2 + c^2) = 8 - d^2 := by
      nlinarith
    rw [h3', h4'] at h2'
    have h6 : (4 - d)^2 - 3 * (8 - d^2) ≤ 0 := by
      nlinarith 
    have h7 : d ^ 2 - 2 * d - 2 ≤ 0 := by
      nlinarith
    nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

  have h20 : max a b ≤ 1 + Real.sqrt 3 := by
    cases max_cases a b with
    | inl h =>
      linarith [h, h8, h12]
    | inr h =>
      linarith [h, h8, h12]

  have h21 : max c d ≤ 1 + Real.sqrt 3 := by
    cases max_cases c d with
    | inl h =>
      linarith [h, h13, h14]
    | inr h =>
      linarith [h, h13, h14]

  cases max_cases (max a b) (max c d) with
  | inl h =>
    linarith [h, h20, h21]
  | inr h =>
    linarith [h, h20, h21]