import Mathlib

theorem inequalities_252467 (x y z : ℝ) (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  have h1 : 0 < x := by linarith
  have h2 : x < 1 := by linarith
  have h3 : 0 < y := by linarith
  have h4 : y < 1 := by linarith
  have h5 : 0 < z := by linarith
  have h6 : z < 1 := by linarith
  have h7 : 0 < (1 - x) := by linarith
  have h8 : 0 < (1 - y) := by linarith
  have h9 : 0 < (1 - z) := by linarith
  have h10 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact h1
    exact h3
    exact h5
  have h11 : 0 < (1 - x) * (1 - y) * (1 - z) := by
    apply mul_pos
    apply mul_pos
    exact h7
    exact h8
    exact h9
  nlinarith [mul_pos h1 h3, mul_pos h1 h5, mul_pos h3 h5,
      mul_pos h7 h8, mul_pos h7 h9, mul_pos h8 h9,
      h10, h11]