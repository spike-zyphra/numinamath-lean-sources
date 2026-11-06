import Mathlib

theorem algebra_21717 : IsLeast {y : ℝ | ∃ x, y = x * (x + 1) * (x + 2) * (x + 3)} (-1) := by
  constructor
  · -- Show that -1 is attainable.
    use (-3 + Real.sqrt 5) / 2
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Show that -1 is a lower bound.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : x * (x + 1) * (x + 2) * (x + 3) = (x^2 + 3 * x + 1)^2 - 1 := by 
      ring
    have h1 : x * (x + 1) * (x + 2) * (x + 3) ≥ -1 := by
      rw [h]
      have h2 : (x^2 + 3 * x + 1)^2 ≥ 0 := by 
        apply sq_nonneg
      linarith
    linarith [hx, h1]