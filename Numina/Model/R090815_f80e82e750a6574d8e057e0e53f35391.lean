import Mathlib

theorem algebra_146642 (a : ℝ) (ha : a ≠ 4) (ha' : a ≠ 2)
    (h : ∃ x y, a * x - (a - 2) * y - 2 = 0 ∧ (a - 1) * x + (4 - a) * y + 2 = 0 ∧ x = 0) :
    a = 3 := by
  rcases h with ⟨x, y, h1, h2, hx⟩
  rw [hx] at h1 h2
  have eq1 : (a - 2) * y = -2 := by 
    linarith 
  have eq2 : (4 - a) * y = -2 := by 
    linarith 
  by_cases hy : y = 0 
  · -- contradiction if y = 0 
    rw [hy] at eq1 
    linarith 
  · -- y ≠ 0 so we can deduce a - 2 = 4 - a
    have h3 : (a - 2) * y = (4 - a) * y := by 
      linarith [eq1, eq2]
    have h4 : a - 2 = 4 - a := by 
      apply (mul_left_inj' hy).mp 
      linarith 
    linarith