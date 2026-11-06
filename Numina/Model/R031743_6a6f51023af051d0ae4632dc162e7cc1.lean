import Mathlib
open Real Set

theorem algebra_9346 (f : Icc (2 : ℝ) 6 → ℝ) (hf : f = λ ⟨x, _⟩ => 3 * sqrt (x - 2) + 4 * sqrt (6 - x)) :
    IsGreatest (range f) 10 := by 
  constructor
  · -- Show that 10 is in the range of f
    use ⟨(86 / 25 : ℝ), by norm_num [mem_Icc]⟩
    rw [hf]
    have h1 : sqrt ((86 / 25 : ℝ) - 2) = 6 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (6 - (86 / 25 : ℝ)) = 8 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp only [h1, h2]
    norm_num
  · -- Show that 10 is the greatest element in the range
    intro y hy
    rcases hy with ⟨⟨x, hx⟩, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have h1 : 2 ≤ x ∧ x ≤ 6 := by
      exact hx
    have h2 : x - 2 ≥ 0 := by
      linarith [h1.1]
    have h3 : 6 - x ≥ 0 := by
      linarith [h1.2]
    have h5 : 3 * sqrt (x - 2) + 4 * sqrt (6 - x) ≤ 10 := by
      nlinarith [sq_nonneg (sqrt (x - 2) - 6 / 5), sq_nonneg (sqrt (6 - x) - 8 / 5),
                  Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (6 - x),
                  mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (6 - x)),
                  Real.sq_sqrt h2, Real.sq_sqrt h3,
                  sq_nonneg ((x - 2) - (6 - x)), mul_nonneg (show 0 ≤ (x - 2 : ℝ) by linarith) (show 0 ≤ (6 - x : ℝ) by linarith)
                ]
    linarith [hfx, h5]