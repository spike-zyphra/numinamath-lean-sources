import Mathlib

theorem algebra_187020 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 1 / x + 1 / y = 5) (h2 : 1 / x ^ 2 + 1 / y ^ 2 = 13) :
    (x = 1 / 3 ∧ y = 1 / 2) ∨ (x = 1 / 2 ∧ y = 1 / 3) := by
  have eq1 : x + y = 5 * (x * y) := by
    field_simp [hx, hy] at h1 ⊢
    linarith
  have eq2 : (x + y) ^ 2 - 2 * (x * y) = 13 * (x * y) ^ 2 := by
    have eq3 : 1 / x ^ 2 + 1 / y ^ 2 = ((x + y) ^ 2 - 2 * (x * y)) / ((x * y) ^ 2) := by 
      field_simp [hx, hy]
      <;> ring
    rw [eq3] at h2 
    have eq4 : (x * y) ^ 2 ≠ 0 := by
      apply pow_ne_zero 2 
      apply mul_ne_zero 
      exact hx
      exact hy 
    field_simp [eq4] at h2 
    nlinarith 
  have eq6 : (5 * (x * y)) ^ 2 - 2 * (x * y) = 13 * (x * y) ^ 2 := by 
    have eq7 : (x + y) ^ 2 - 2 * (x * y) = 13 * (x * y) ^ 2 := eq2 
    rw [show x + y = 5 * (x * y) by linarith [eq1]] at eq7 
    linarith
  have h3 : x * y = 0 ∨ x * y = 1 / 6 := by 
    have h4 : (5 * (x * y) )^2 - 2 * (x * y) = 13 * (x * y) ^ 2 := eq6 
    have h5 : x * y * (6 * (x * y) - 1) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7 
    · -- Case x * y = 0 
      left
      linarith 
    · -- Case 6 * (x * y) - 1 = 0 
      right 
      linarith 
  have h4 : x * y = 1 / 6 := by 
    cases h3 with
    | inl h5 => 
      have h5' : x * y = 0 := h5 
      have h6 : x = 0 ∨ y = 0 := by 
        cases (mul_eq_zero.mp h5') with 
        | inl h7 => 
          left 
          linarith 
        | inr h8 => 
          right 
          linarith 
      cases h6 with 
      | inl h7 => 
        exfalso 
        apply hx 
        linarith 
      | inr h8 => 
        exfalso 
        apply hy 
        linarith 
    | inr h5 => 
      linarith 
  have eq5 : x + y = 5 / 6 := by 
    nlinarith [h4, eq1]
  have h3quad : (x - 1 / 2) * (x - 1 / 3) = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 3), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, h4, eq5]
  cases' (mul_eq_zero.mp h3quad) with h41 h42
  · -- Case x - 1/2 = 0, so x = 1/2. Then y = 1/3.
    have hx2 : x = 1 / 2 := by linarith 
    have hy3 : y = 1 / 3 := by 
      nlinarith 
    right 
    exact ⟨hx2, hy3⟩ 
  · -- Case x - 1/3 = 0, so x = 1/3. Then y = 1/2.
    have hx3 : x = 1 / 3 := by linarith 
    have hy2 : y = 1 / 2 := by 
      nlinarith 
    left 
    exact ⟨hx3, hy2⟩