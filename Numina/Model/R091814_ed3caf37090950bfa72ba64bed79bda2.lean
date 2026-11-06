import Mathlib

theorem algebra_318557 (m : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ x1 ∈ Set.Ioo (-2) (-1) ∧ x2 ∈ Set.Ioo 2 3 ∧
    2*x1^2-3*x1+m=0 ∧ 2*x2^2-3*x2+m=0) :
    -9 < m ∧ m < -5 := by
  rcases h with ⟨x1, x2, hx12, hx1, hx2, h1, h2⟩
  rw [Set.mem_Ioo] at hx1 hx2
  have h3 : -2 < x1 := hx1.1
  have h4 : x1 < -1 := hx1.2
  have h5 : 2 < x2 := hx2.1
  have h6 : x2 < 3 := hx2.2
  have h7 : m > -14 := by
    nlinarith [sq_pos_of_ne_zero (show x1 + 2 ≠ 0 by linarith), sq_pos_of_ne_zero (show x1 + 1 ≠ 0 by linarith), h1]
  have h8 : m < -5 := by
    nlinarith [sq_pos_of_ne_zero (show x1 + 2 ≠ 0 by linarith), sq_pos_of_ne_zero (show x1 + 1 ≠ 0 by linarith), h1]
  have hm1 : -9 < m := by
    nlinarith [sq_pos_of_ne_zero (show x1 + 2 ≠ 0 by linarith), sq_pos_of_ne_zero (show x1 + 1 ≠ 0 by linarith), h1]
  exact ⟨hm1, h8⟩