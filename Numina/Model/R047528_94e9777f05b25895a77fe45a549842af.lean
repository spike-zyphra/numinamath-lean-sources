import Mathlib

theorem algebra_255496 :
  { x : ℝ | ∃ (m n : ℝ), m + n ≠ 0 ∧ 
    x^2 / (m + n)^2 - 4 * m * n / (m + n)^2 * x - (m - n)^2 = 0 } =
  { x : ℝ | ∃ (m n : ℝ), m + n ≠ 0 ∧ (x = (m + n)^2 ∨ x = -(m - n)^2) } := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor 
  · -- Assume x is in left side, prove in right side
    rintro ⟨m, n, hm, heq⟩
    have eq1 : x^2 - 4 * m * n * x - (m - n) ^ 2 * (m + n) ^ 2 = 0 := by 
      have h1 : (m + n) ^ 2 ≠ 0 := by
        apply pow_ne_zero 2 
        exact hm 
      have eq2 : x^2 / (m + n) ^ 2 - 4 * m * n / (m + n) ^ 2 * x - (m - n) ^ 2 = 0 := heq 
      field_simp [h1] at eq2 ⊢ 
      nlinarith 
    have eq2 : (x - (m + n) ^ 2) * (x + (m - n) ^ 2) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp eq2) with h h 
    · -- x - (m + n)^2 = 0, so x = (m + n)^2 
      have hx : x = (m + n) ^ 2 := by linarith 
      refine ⟨m, n, hm, Or.inl hx⟩ 
    · -- x + (m - n)^2 = 0, so x = -(m - n)^2 
      have hx : x = -(m - n) ^ 2 := by linarith
      refine ⟨m, n, hm, Or.inr hx⟩
  · -- Assume x is in right side, prove in left side
    rintro ⟨m, n, hm, h⟩
    rcases h with (h | h)
    · -- Case where x = (m + n)^2
      use m, n 
      constructor 
      · exact hm 
      · -- Show that x is a solution to the equation 
        rw [h] 
        field_simp [show m + n ≠ 0 by exact hm] 
        nlinarith
    · -- Case where x = -(m - n)^2
      use m, n 
      constructor 
      · exact hm 
      · -- Show that x is a solution to the equation 
        rw [h]
        field_simp [show m + n ≠ 0 by exact hm] 
        nlinarith