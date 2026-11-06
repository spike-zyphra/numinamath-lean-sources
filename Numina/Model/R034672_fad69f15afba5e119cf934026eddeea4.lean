import Mathlib

theorem algebra_2492 (x y : ℤ) : (y^4 - 8 * y^2 + 7 = 8 * x^2 - 2 * x^2 * y^2 - x^4) ↔
    (x, y) = (0, 1) ∨ (x, y) = (0, -1) ∨ (x, y) = (1, 0) ∨ (x, y) = (-1, 0) := by 
  constructor
  · -- Assume the equation holds, prove the four possibilities
    intro h_eq
    have h1 : (y^2 + x^2 : ℤ) ^ 2 - 8 * (y^2 + x^2 : ℤ) + 7 = 0 := by
      nlinarith [h_eq]
    have h2 : ((y^2 + x^2 : ℤ) - 1) * ((y^2 + x^2 : ℤ) - 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case $y^2 + x^2 - 1 = 0$, so $y^2 + x^2 = 1$
      have h5 : (y^2 + x^2 : ℤ) = 1 := by linarith
      have h6 : x^2 + y^2 = 1 := by
        nlinarith
      have h7 : x ≤ 1 := by nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y : ℤ), h6]
      have h8 : x ≥ -1 := by nlinarith [sq_nonneg (x + 1 : ℤ), sq_nonneg (y : ℤ), h6]
      have h9 : y ≤ 1 := by nlinarith [sq_nonneg (y - 1 : ℤ), sq_nonneg (x : ℤ), h6]
      have h10 : y ≥ -1 := by nlinarith [sq_nonneg (y + 1 : ℤ), sq_nonneg (x : ℤ), h6]
      interval_cases x <;> interval_cases y <;> simp [Prod.ext_iff] at *
      <;> tauto
    · -- Case $y^2 + x^2 - 7 = 0$, so $y^2 + x^2 = 7$
      have h5 : (y^2 + x^2 : ℤ) = 7 := by linarith
      have h6 : x^2 + y^2 = 7 := by 
        nlinarith
      have h7 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
        have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
          omega 
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have h8 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
        have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
          omega 
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      omega 
  · -- Show that the four points satisfy the equation
    rintro (h_eq | h_eq | h_eq | h_eq)
    · -- Case (x, y) = (0, 1)
      simp [Prod.mk.injEq] at h_eq 
      rcases h_eq with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x, y) = (0, -1)
      simp [Prod.mk.injEq] at h_eq 
      rcases h_eq with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x, y) = (1, 0)
      simp [Prod.mk.injEq] at h_eq 
      rcases h_eq with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x, y) = (-1, 0)
      simp [Prod.mk.injEq] at h_eq 
      rcases h_eq with ⟨rfl, rfl⟩ 
      norm_num