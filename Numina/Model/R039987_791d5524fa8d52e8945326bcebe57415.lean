import Mathlib

theorem algebra_108289 (a b c : ℝ) (ha : a ≠ 0) (hroots : ¬∃ x : ℝ, a * x ^ 2 + b * x + c = 0)
    (hsum : a + b + c < 0) : c < 0 := by
  by_contra h
  push_neg at h
  have h1 : b ^ 2 < 4 * a * c := by
    by_contra h2
    push_neg at h2
    have h3 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
      have h4 : b ^ 2 - 4 * a * c ≥ 0 := by nlinarith
      use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      field_simp [ha]
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith
    contradiction
  -- `h` is c >= 0 
  -- `ha` is a ≠ 0
  -- `hsum` is a + b + c < 0
  -- `h1` is b^2 < 4*a*c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b + 2*a), sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b + 2*a), sq_pos_of_ne_zero ha, hsum, sq_nonneg (a + b - c)]