import Mathlib

theorem algebra_239557 (a b : ℝ) (h : ∃ x y, x ∈ Set.Icc 1 2 ∧ y ∈ Set.Icc 1 2 ∧
    x^2 + a * x + b - 3 = 0 ∧ y^2 + a * y + b - 3 = 0) :
    a^2 + (b - 4)^2 ≥ 2 := by
  rcases h with ⟨x, y, hx, hy, h1, h2⟩
  rw [Set.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  nlinarith [sq_nonneg (a + x), sq_nonneg (b - 3 -1), sq_nonneg (x -1), sq_nonneg (x -2),
          sq_nonneg (y -1), sq_nonneg (y -2),
          mul_nonneg (show (0 : ℝ) ≤ x -1 by nlinarith) (show (0 : ℝ) ≤ 2 -x by nlinarith),
          mul_nonneg (show (0 : ℝ) ≤ y -1 by nlinarith) (show (0 : ℝ) ≤ 2 -y by nlinarith)]