import Mathlib

theorem algebra_325670 {a b c : ℝ} (ha : a ≠ 0) (hvertex : ∀ x, a * x ^ 2 + b * x + c = a * (x - 4) ^ 2 - 11)
    (hroots : ∃ x1 x2, x1 > 0 ∧ x2 < 0 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    a > 0 := by
  rcases hroots with ⟨x1, x2, hx1_pos, hx2_neg, heq1, heq2⟩
  have h1 := hvertex x1
  rw [heq1] at h1
  have eq1' : a * (x1 - 4) ^ 2 = 11 := by linarith
  have h2 := hvertex x2
  rw [heq2] at h2
  have eq2' : a * (x2 - 4) ^ 2 = 11 := by linarith 
  have h5 : (x1 - 4) ^ 2 > 0 := by 
    nlinarith [sq_nonneg (x1 - 4), hx1_pos]
  have h6 : (x2 - 4) ^ 2 > 0 := by 
    nlinarith [sq_nonneg (x2 - 4), hx2_neg]
  have ha1 : a > 0 := by 
    nlinarith 
  exact ha1