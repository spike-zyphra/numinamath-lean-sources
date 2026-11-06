import Mathlib

  theorem algebra_113507 (x y : ℝ) (hx : x ∈ Set.Icc (-7) 1) (hy : y ∈ Set.Icc (-1) 7) :
    x^2 + y^2 + 6 * (x - y) ∈ Set.Icc (-18) 14 := by 
  rw [Set.mem_Icc] at hx hy ⊢
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  constructor
  · -- Proving the lower bound (-18)
    nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 3)]
  · -- Proving the upper bound (14)
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 7), sq_nonneg (x + 7), sq_nonneg (y + 1)]