import Mathlib

theorem algebra_114932 {p1 p2 q1 q2 : ℝ}
    (h : p1 * p2 = 2 * (q1 + q2)) :
    ∃ x, x^2 + p1 * x + q1 = 0 ∨ x^2 + p2 * x + q2 = 0 := by
  by_cases hp₁ : p1 ^ 2 - 4 * q1 ≥ 0
  · -- If the discriminant of the first quadratic is non-negative
    have : ∃ x, x^2 + p1 * x + q1 = 0 := by
      use (-p1 + Real.sqrt (p1 ^ 2 - 4 * q1)) / 2
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      linarith
    rcases this with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  · -- Assume the discriminant of the first quadratic is negative
    by_cases hp₂ : p2 ^ 2 - 4 * q2 ≥ 0
    · -- If the discriminant of the second quadratic is non-negative
      have : ∃ x, x^2 + p2 * x + q2 = 0 := by
        use (-p2 + Real.sqrt (p2 ^ 2 - 4 * q2)) / 2
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        linarith
      rcases this with ⟨x, hx⟩
      exact ⟨x, Or.inr hx⟩
    · -- Assume both discriminants are negative
      -- So we have $p_1^2 < 4q_1$ and $p_2^2 < 4q_2$
      have h₁ : p1 ^ 2 < 4 * q1 := by linarith
      have h₂ : p2 ^ 2 < 4 * q2 := by linarith
      -- Adding both inequalities
      have h₃ : p1 ^ 2 + p2 ^ 2 < 4 * (q1 + q2) := by linarith
      -- From h: $p_1 * p_2 = 2 * (q1 + q2)$, we can write $2 * (p_1 * p_2) = 4 * (q1 + q2)$
      have h₄ : 2 * (p1 * p2) = 4 * (q1 + q2) := by linarith [h]
      -- So $p_1^2 + p_2^2 < 2 * (p_1 * p_2)$
      have h₅ : p1 ^ 2 + p2 ^ 2 < 2 * (p1 * p2) := by linarith [h₃, h₄]
      -- i.e., $(p1 - p2)^2 < 0$
      have h₆ : (p1 - p2) ^ 2 < 0 := by
        linarith [h₅]
      -- But $(p1 - p2)^2 ≥ 0$
      have h₇ : (p1 - p2) ^ 2 ≥ 0 := by
        exact sq_nonneg (p1 - p2)
      -- So we get a contradiction
      linarith