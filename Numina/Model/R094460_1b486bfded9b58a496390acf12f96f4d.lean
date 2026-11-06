import Mathlib

theorem inequalities_214295 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    2*(x^3+y^3+z^3)-(x^2*y+y^2*z+z^2*x) ≤ 3 := by 
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_nonneg (show 0 ≤ (1 - x) by linarith) (show 0 ≤ (1 - y) by linarith),
    mul_nonneg (show 0 ≤ (1 - y) by linarith) (show 0 ≤ (1 - z) by linarith),
    mul_nonneg (show 0 ≤ (1 - z) by linarith) (show 0 ≤ (1 - x) by linarith)]