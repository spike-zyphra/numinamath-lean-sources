import Mathlib

open Real

theorem inequalities_82355 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + y + x * y = 3) :
    x + y ≥ 2 ∧ (x + y = 2 ↔ x = 1 ∧ y = 1) := by 
  have h1 : (x + 1) * (y + 1) = 4 := by
    nlinarith
  
  have h2 : x + y ≥ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 1)]
  
  have h_eq_iff : x + y = 2 ↔ x = 1 ∧ y = 1 := by
    constructor
    · -- Assume x + y = 2, prove x = 1 ∧ y = 1
      intro h_eq
      have h_eq1 : x * y = 1 := by
        nlinarith [h, h_eq]
      have h_eq2 : x = 1 := by
        nlinarith [h_eq1, h_eq, sq_nonneg (x - 1), sq_nonneg (y - 1)]
      have h_eq3 : y = 1 := by
        nlinarith [h_eq2, h_eq]
      exact ⟨h_eq2, h_eq3⟩

    · -- Assume x = 1 ∧ y = 1, prove x + y = 2
      rintro ⟨rfl, rfl⟩
      norm_num
  
  constructor
  · exact h2
  · exact h_eq_iff