import Mathlib

theorem inequalities_197467 (x : ℝ) (hx : x ≠ 3) :
    (x^2 - abs x - 12) / (x - 3) ≥ 2 * x ↔ x < 3 := by
  constructor
  · -- Assume $\frac{x^2 - |x| - 12}{x - 3} \geq 2x$, we need to prove $x < 3$
    intro h
    by_contra h1
    push_neg at h1
    have h2 : x ≥ 3 := by linarith
    have h3 : x > 3 := by
      by_contra h4
      push_neg at h4
      have h4' : x = 3 := by linarith
      contradiction
    have h4 : abs x = x := by
      rw [abs_of_nonneg]
      linarith
    have h5 : x - 3 > 0 := by linarith
    have h6 : x^2 - abs x - 12 ≥ 2 * x * (x - 3) := by
      have h7 : (x^2 - abs x - 12) / (x - 3) ≥ 2 * x := h
      have h8 : x^2 - abs x - 12 ≥ 2 * x * (x - 3) := by
        have pos1 : x - 3 > 0 := h5
        have h9 : (x^2 - abs x - 12) / (x - 3) - 2 * x ≥ 0 := by
          linarith
        have h10 : (x^2 - abs x - 12 - 2 * x * (x - 3)) / (x - 3) ≥ 0 := by
          have h11 : (x^2 - abs x - 12) / (x - 3) - 2 * x = (x^2 - abs x - 12 - 2 * x * (x - 3)) / (x - 3) := by
            field_simp [(show x - 3 ≠ 0 by intro h11; apply hx; linarith)]
            <;> ring
          nlinarith [h11, h9]
        apply (div_nonneg_iff).mp at h10
        cases h10 with
        | inl h11 =>
          nlinarith
        | inr h12 =>
          nlinarith
      linarith
    rw [h4] at h6
    nlinarith [sq_nonneg (x - 5 / 2)]
  · -- Assume x < 3 and prove $\frac{x^2 - |x| - 12}{x - 3} \geq 2x$
    intro h
    have h1 : x < 3 := by linarith
    by_cases h2 : x ≥ 0
    · -- Assume 0 ≤ x < 3
      have h3 : abs x = x := by
        rw [abs_of_nonneg]
        linarith
      have h4 : (x^2 - abs x - 12) / (x - 3) ≥ 2 * x := by
        have h5 : x - 3 < 0 := by linarith
        have h6 : (x^2 - abs x - 12) ≤ 2 * x * (x - 3) := by
          rw [h3]
          nlinarith [sq_nonneg (x - 5 / 2)]
        apply (le_div_iff_of_neg' (by linarith)).mpr
        linarith
      linarith
    · -- Assume x < 0
      have h3 : abs x = -x := by
        rw [abs_of_neg]
        linarith
      have h4 : (x^2 - abs x - 12) / (x - 3) ≥ 2 * x := by
        have h5 : x - 3 < 0 := by linarith
        have h6 : (x^2 - abs x - 12) ≤ 2 * x * (x - 3) := by
          rw [h3]
          nlinarith [sq_nonneg (x), sq_nonneg (x - 4)]
        apply (le_div_iff_of_neg' (by linarith)).mpr
        linarith
      linarith