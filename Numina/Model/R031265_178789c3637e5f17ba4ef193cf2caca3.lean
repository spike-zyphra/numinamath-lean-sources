import Mathlib

theorem inequalities_170849 (x : ℝ) (hx : ∀ p ∈ Set.Icc 0 4, x^2 + p * x > 4 * x + p - 3) :
    x > 3 ∨ x < -1 := by
  have h1 := hx 0 (by norm_num)
  have h2 : x^2 - 4 * x + 3 > 0 := by
    linarith
  have h3 : (x - 1) * (x - 3) > 0 := by
    nlinarith
  have h4 := hx 4 (by norm_num)
  have h5 : x ^ 2 - 1 > 0 := by
    nlinarith
  by_cases h6 : x < 1
  · -- If $x < 1$, from $x^2 - 1 > 0$ we get $x < -1$
    have h7 : x < -1 := by
      nlinarith [h5]
    right
    linarith
  · -- If $x \geq 1$, from $(x - 1)(x - 3) > 0$ we get $x > 3$
    have h8 : x ≥ 1 := by
      by_contra h
      push_neg at h
      have : x < 1 := by linarith
      linarith [h6, this]
    have h9 : x > 3 := by
      nlinarith [h3, h8]
    left
    linarith