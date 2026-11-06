import Mathlib

theorem algebra_149910 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x, a * x ^ 2 + 2 * b * x + c = 0 ∨ b * x ^ 2 + 2 * c * x + a = 0 ∨
    c * x ^ 2 + 2 * a * x + b = 0 := by
  by_cases h1 : (4 * b ^ 2 - 4 * a * c) ≥ 0
  · -- If the first discriminant is non-negative, then we can solve the first quadratic.
    use (-2 * b + Real.sqrt (4 * b ^ 2 - 4 * a * c)) / (2 * a)
    left
    field_simp [ha]
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    linarith
  · -- If the first discriminant is negative, we need to check the second.
    by_cases h2 : (4 * c ^ 2 - 4 * b * a) ≥ 0
    · -- If the second discriminant is non-negative, we can solve the second quadratic.
      use (-2 * c + Real.sqrt (4 * c ^ 2 - 4 * b * a)) / (2 * b)
      right
      left
      field_simp [hb]
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      linarith
    · -- If the second discriminant is negative, the third discriminant must be non-negative.
      by_cases hc : c = 0
      · -- If c = 0
        use (-b) / (2 * a)
        right
        right
        rw [show c = 0 by linarith [hc]]
        field_simp [ha]
        all_goals nlinarith
      · -- If c ≠ 0
        have hc' : c ≠ 0 := hc
        have h3 : (4 * a ^ 2 - 4 * c * b) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
        use (-2 * a + Real.sqrt (4 * a ^ 2 - 4 * c * b)) / (2 * c)
        right
        right
        field_simp [hc']
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith