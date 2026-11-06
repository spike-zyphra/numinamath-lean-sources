import Mathlib

theorem algebra_106693 (a b c d : ℤ) (h : ∀ m n : ℤ, ∃ x y : ℤ,
    a * x + b * y = m ∧ c * x + d * y = n) :
    a * d - b * c = 1 ∨ a * d - b * c = -1 := by
  have h1 := h 1 0
  rcases h1 with ⟨x1, y1, h1, h2⟩
  have h3 := h 0 1
  rcases h3 with ⟨x2, y2, h3, h4⟩
  have eq1 : a * x1 + b * y1 = 1 := h1
  have eq2 : c * x1 + d * y1 = 0 := h2
  have eq3 : a * x2 + b * y2 = 0 := h3
  have eq4 : c * x2 + d * y2 = 1 := h4
  have h5 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := by
    nlinarith [eq1, eq2, eq3, eq4]
  apply Int.eq_one_or_neg_one_of_mul_eq_one 
  exact h5