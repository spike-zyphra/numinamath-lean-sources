import Mathlib

theorem algebra_275216 (a : ℤ) (h : ∃ x1 x2 x3 : ℤ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    abs (abs (x1 - 2) - 1) = a ∧ abs (abs (x2 - 2) - 1) = a ∧ abs (abs (x3 - 2) - 1) = a) :
    a = 1 := by
  rcases h with ⟨x1, x2, x3, h1, h2, h3, h11, h22, h33⟩
  have eq1 : abs (abs (x1 - 2) - 1) = a := h11
  have eq2 : abs (abs (x2 - 2) - 1) = a := h22
  have eq3 : abs (abs (x3 - 2) - 1) = a := h33
  cases' abs_cases (abs (x1 - 2) - 1) with h111 h111 <;> 
    cases' abs_cases (x1 - 2) with h12 h12 <;> 
      cases' abs_cases (abs (x2 - 2) - 1) with h211 h211 <;> 
        cases' abs_cases (x2 - 2) with h22 h22 <;> 
          cases' abs_cases (abs (x3 - 2) - 1) with h311 h311 <;> 
            cases' abs_cases (x3 - 2) with h32 h32 <;> 
              omega