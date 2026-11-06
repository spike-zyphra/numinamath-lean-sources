import Mathlib

theorem algebra_303846 (f : ℝ → ℝ) (hf : f = fun x => 2 * x + Real.sqrt (6 - x)) :
    IsGreatest (Set.image f {x | x ≤ 6}) (12 + 1 / 8) := by
  have h1 : ∀ x, f x = 2 * x + Real.sqrt (6 - x) := by
    intro x
    rw [hf]

  constructor
  · -- Show that 12 + 1/8 is in the image
    use 95 / 16
    constructor
    · -- Show that 95/16 ≤ 6
      norm_num
    · -- Show that f(95/16) = 12 + 1/8
      rw [h1]
      have h2 : Real.sqrt (6 - (95 / 16 : ℝ)) = 1 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      norm_num
  · -- Show that 12 + 1/8 is the greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have h2 : x ≤ (6 : ℝ) := by
      simpa using hx

    have eq1 : f x = 2 * x + Real.sqrt (6 - x) := h1 x
    rw [eq1] at hfx

    have h3 : 2 * x + Real.sqrt (6 - x) ≤ (12 + (1 / 8 : ℝ)) := by
      nlinarith [sq_nonneg (Real.sqrt (6 - x) - 1 / 4), sq_nonneg (x - 95 / 16),
                Real.sqrt_nonneg (6 - x),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (6 - x) by linarith),
                mul_nonneg (Real.sqrt_nonneg (6 - x)) (Real.sqrt_nonneg (6 - x))
                  ]

    linarith [h3, hfx]