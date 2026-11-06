import Mathlib
open Real Set

theorem algebra_8982 (f : ℝ → ℝ) (hf : f = λ x => x * (6 - 2 * x) ^ 2) :
  IsGreatest (image f (Icc 0 3)) 16 := by
  constructor
  · -- Show that 16 belongs to the image of f over [0, 3]
    rw [hf]
    simp only [image, Set.mem_setOf_eq, Set.mem_setOf_eq]
    use 1
    constructor
    · -- Show that 1 is in the interval [0, 3]
      exact ⟨by norm_num, by norm_num⟩
    · -- Calculate f(1)
      norm_num
  · -- Show that for any y in the image, y ≤ 16
    intro y hy
    rw [hf] at *
    simp at hy ⊢
    rcases hy with ⟨x, ⟨h0, h3⟩, hfx⟩
    have h1 : x * (6 - 2 * x) ^ 2 ≤ 16 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (6 - 2 * x), sq_nonneg (x - 2), sq_nonneg (x - 3)]
    linarith