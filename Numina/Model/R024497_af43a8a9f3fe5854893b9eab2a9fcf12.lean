import Mathlib

theorem inequalities_600598 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≠ 0 ∨ b ≠ 0) (h2 : a ≠ 0 ∨ c ≠ 0) (h3 : b ≠ 0 ∨ c ≠ 0) :
    a^2 / ((2 * a + b) * (2 * a + c)) + b^2 / ((2 * b + c) * (2 * b + a)) +
    c^2 / ((2 * c + a) * (2 * c + b)) ≤ 1 / 3 := by
  have h4 : 2 * a + b ≠ 0 := by
    by_contra h
    have h5 : a = 0 := by
      nlinarith
    have h6 : b = 0 := by
      nlinarith
    have h5' : a = 0 := h5
    have h6' : b = 0 := h6
    have h1' : a ≠ 0 ∨ b ≠ 0 := h1
    cases h1' with
    | inl h7 =>
      exfalso
      exact h7 (by linarith)
    | inr h8 =>
      exfalso
      exact h8 (by linarith)
  have h5 : 2 * a + c ≠ 0 := by
    by_contra h
    have h5 : a = 0 := by
      nlinarith
    have h6 : c = 0 := by
      nlinarith
    have h5' : a = 0 := h5
    have h6' : c = 0 := h6
    have h2' : a ≠ 0 ∨ c ≠ 0 := h2
    cases h2' with
    | inl h7 =>
      exfalso
      exact h7 (by linarith)
    | inr h8 =>
      exfalso
      exact h8 (by linarith)
  have h6 : 2 * b + c ≠ 0 := by
    by_contra h
    have h7 : b = 0 := by
      nlinarith
    have h8 : c = 0 := by
      nlinarith
    have h7' : b = 0 := h7
    have h8' : c = 0 := h8
    have h3' : b ≠ 0 ∨ c ≠ 0 := h3
    cases h3' with
    | inl h9 =>
      exfalso
      exact h9 (by linarith)
    | inr h10 =>
      exfalso
      exact h10 (by linarith)
  have h7 : 2 * b + a ≠ 0 := by
    by_contra h
    have h8 : b = 0 := by
      nlinarith
    have h9 : a = 0 := by
      nlinarith
    have h8' : b = 0 := h8
    have h9' : a = 0 := h9
    have h1' : a ≠ 0 ∨ b ≠ 0 := h1
    cases h1' with
    | inl h7 =>
      exfalso
      exact h7 (by linarith)
    | inr h8 =>
      exfalso
      exact h8 (by linarith)
  have h8 : 2 * c + a ≠ 0 := by
    by_contra h
    have h4 : c = 0 := by
      nlinarith
    have h5 : a = 0 := by
      nlinarith
    have h4' : c = 0 := h4
    have h5' : a = 0 := h5
    have h2' : a ≠ 0 ∨ c ≠ 0 := h2
    cases h2' with
    | inl h7 =>
      exfalso
      exact h7 (by linarith)
    | inr h8 =>
      exfalso
      exact h8 (by linarith)
  have h9 : 2 * c + b ≠ 0 := by
    by_contra h
    have h10 : c = 0 := by
      nlinarith
    have h11 : b = 0 := by
      nlinarith
    have h10' : c = 0 := h10
    have h11' : b = 0 := h11
    have h3' : b ≠ 0 ∨ c ≠ 0 := h3
    cases h3' with
    | inl h9 =>
      exfalso
      exact h9 (by linarith)
    | inr h10 =>
      exfalso
      exact h10 (by linarith)
  have h10 : a ^ 2 / ((2 * a + b) * (2 * a + c)) + b ^ 2 / ((2 * b + c) * (2 * b + a)) + c ^ 2 / ((2 * c + a) * (2 * c + b)) - 1 / 3 ≤ 0 := by
    have h11 : a ^ 2 / ((2 * a + b) * (2 * a + c)) + b ^ 2 / ((2 * b + c) * (2 * b + a)) + c ^ 2 / ((2 * c + a) * (2 * c + b)) - 1 / 3 =
          ( (a^2 * ((2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) + b^2 * ((2 * c + a) * (2 * c + b) * (2 * a + b) * (2 * a + c)) + c^2 * ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a)) - 1/3 * ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) ) / ((2 * a + b) * (2 * a + c) * (2 * b + c) * (2 * b + a) * (2 * c + a) * (2 * c + b)) )
      := by
      field_simp [h4, h5, h6, h7, h8, h9]
      ring_nf
    rw [h11]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
    ]
    positivity
  linarith