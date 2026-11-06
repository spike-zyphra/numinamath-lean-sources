import Mathlib

theorem algebra_111897 (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (1 + 1 / x : ℚ) * (1 + 1 / y : ℚ) = 3 / 2) :
    (x = 3 ∧ y = 8) ∨ (x = 4 ∧ y = 5) ∨ (x = 8 ∧ y = 3) ∨ (x = 5 ∧ y = 4) := by
  have h1 : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have h2 : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have eq1 : (1 + 1 / x : ℚ) * (1 + 1 / y : ℚ) = (3 / 2 : ℚ) := h
  have eq2 : (2 * ((x : ℚ) + 1) * ((y : ℚ) + 1) : ℚ) = (3 * (x : ℚ) * (y : ℚ) : ℚ) := by
    field_simp [h1, h2] at eq1 ⊢
    linarith
  have eq3 : 2 * (x + 1) * (y + 1) = 3 * x * y := by
    have eq3' : (2 * ((x + 1) : ℕ) * (y + 1 : ℕ) : ℕ) = (3 * (x : ℕ) * (y : ℕ) : ℕ) := by
      have eq2_nat : (2 * ((x : ℚ) + 1) * ((y : ℚ) + 1) : ℚ) = (3 * (x : ℚ) * (y : ℚ) : ℚ) := eq2
      exact_mod_cast eq2_nat
    linarith
  have eq4 : x ≤ 8 := by
    by_contra h
    push_neg at h
    have h3 : y ≤ 8 := by
      nlinarith [sq_nonneg ((x : ℕ) - 8 : ℤ), sq_nonneg ((y : ℕ) - 8 : ℤ), 
        mul_pos (show 0 < (x : ℕ) by omega) (show 0 < (y : ℕ) by omega), 
          sq_pos_of_pos (show 0 < (x : ℕ) by omega), 
            sq_pos_of_pos (show 0 < (y : ℕ) by omega)
        ]
    interval_cases y <;> omega
  have eq5 : y ≤ 8 := by
    by_contra h
    push_neg at h
    have h3 : x ≤ 8 := by
      nlinarith [sq_nonneg ((x : ℕ) - 8 : ℤ), sq_nonneg ((y : ℕ) - 8 : ℤ), 
        mul_pos (show 0 < (x : ℕ) by omega) (show 0 < (y : ℕ) by omega), 
          sq_pos_of_pos (show 0 < (x : ℕ) by omega), 
            sq_pos_of_pos (show 0 < (y : ℕ) by omega)
        ]
    interval_cases x <;> omega
  interval_cases x <;> interval_cases y
    <;> norm_num at eq3
    <;> norm_num at h
    <;> tauto