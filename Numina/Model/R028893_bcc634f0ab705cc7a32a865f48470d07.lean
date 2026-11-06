import Mathlib

theorem number_theory_210108 (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (1 / x : ℚ) + (1 / y : ℚ) = 1 / 3) :
    x = 4 ∨ x = 6 ∨ x = 12 := by
  have h1 : (x : ℚ) ≠ 0 := by
    exact_mod_cast hx
  have h2 : (y : ℚ) ≠ 0 := by
    exact_mod_cast hy

  have h3 : (x * y : ℚ) = 3 * (x + y : ℚ) := by
    field_simp [h1, h2] at h ⊢
    linarith
  have h4 : (x * y : ℕ) = 3 * (x + y : ℕ) := by
    exact_mod_cast h3
  have h5 : x ≤ 12 := by 
    by_contra h
    push_neg at h
    have h6 : y ≤ 3 := by
      nlinarith [h4, h]
    interval_cases y <;> omega
  have h6 : y ≤ 12 := by 
    by_contra h
    push_neg at h
    have h7 : x ≤ 3 := by
      nlinarith [h4, h]
    interval_cases x <;> omega
  interval_cases x <;> omega