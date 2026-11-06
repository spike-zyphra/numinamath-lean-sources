import Mathlib

theorem number_theory_298333 {x y : ℕ} (h₀ : x < y) (h₁ : x^3 + 19 * y = y^3 + 19 * x) : x + y = 5 := by
  have eq1 : (x : ℤ)^3 + 19 * (y : ℤ) = (y : ℤ)^3 + 19 * (x : ℤ) := by
    exact_mod_cast h₁
  have eq2 : (x - y : ℤ) * ((x : ℤ)^2 + (x : ℤ) * (y : ℤ) + (y : ℤ)^2 - 19) = 0 := by
    nlinarith [sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) + (y : ℤ)), sq_nonneg ((x : ℤ) ^ 2 - (y : ℤ) ^ 2)]
  have eq3 : (x - y : ℤ) = 0 ∨ ((x : ℤ)^2 + (x : ℤ) * (y : ℤ) + (y : ℤ)^2 - 19) = 0 := by
    cases (mul_eq_zero.mp eq2) with
    | inl h =>
      tauto
    | inr h =>
      tauto
  have eq4 : ((x : ℤ)^2 + (x : ℤ) * (y : ℤ) + (y : ℤ)^2 - 19) = 0 := by
    by_contra h
    push_neg at h
    have eq5 : (x - y : ℤ) = 0 := by
      tauto
    have eq6 : (x : ℤ) = (y : ℤ) := by 
      linarith
    have eq7 : (x : ℕ) = (y : ℕ) := by
      exact_mod_cast eq6
    nlinarith
  have h8 : (x : ℕ) ≤ 4 := by
    nlinarith [sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) + (y : ℤ)), 
      sq_nonneg ((y : ℤ) ^ 2 - (x : ℤ) ^ 2), sq_nonneg ((x : ℤ) * (y : ℤ)), 
      sq_nonneg ((y : ℤ) ^ 2 + (x : ℤ) ^ 2), h₀]
  have h10 : (y : ℕ) ≤ 4 := by
    nlinarith [sq_nonneg ((y : ℤ) - (x : ℤ)), sq_nonneg ((x : ℤ) + (y : ℤ)), 
      sq_nonneg ((y : ℤ) ^ 2 - (x : ℤ) ^ 2), sq_nonneg ((x : ℤ) * (y : ℤ)), 
      sq_nonneg ((y : ℤ) ^ 2 + (x : ℤ) ^ 2), h₀, sq_nonneg ((x : ℤ) - (4 : ℤ)), sq_nonneg ((y : ℤ) - (4 : ℤ)), h8]
  interval_cases x <;> interval_cases y <;> omega