import Mathlib

theorem algebra_170919 {x y z : ℝ} (h1 : 2*x^2/(1+x^2)=y) (h2 : 2*y^2/(1+y^2)=z)
    (h3 : 2*z^2/(1+z^2)=x) :
    (x=0 ∧ y = 0 ∧ z = 0 ) ∨ (x=1 ∧ y = 1 ∧ z = 1) := by
  by_cases hx : x = 0
  · -- Assume x = 0
    rw [hx] at h1
    simp at h1
    have hy : y = 0 := by linarith
    rw [hy] at h2
    simp at h2
    have hz : z = 0 := by linarith
    left
    exact ⟨hx, hy, hz⟩
  · -- Assume x ≠ 0
    have h1' : 2 * x ^ 2 = y * (1 + x ^ 2) := by
      have h1'' : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [h1''] at h1 
      linarith
    have h2' : 2 * y ^ 2 = z * (1 + y ^ 2) := by
      have h2'' : 1 + y ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg y]
      field_simp [h2''] at h2
      linarith
    have h3' : 2 * z ^ 2 = x * (1 + z ^ 2) := by
      have h3'' : 1 + z ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg z]
      field_simp [h3''] at h3
      linarith
    -- Show that variables are non-negative
    have h4 : y ≥ 0 := by
      nlinarith [sq_nonneg x]
    have h5 : z ≥ 0 := by
      nlinarith [sq_nonneg y]
    have h6 : x ≥ 0 := by
      nlinarith [sq_nonneg z]
    -- Show that variables are equal
    have h7 : x = y := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg (show (0 : ℝ) ≤ x by nlinarith) (show (0 : ℝ) ≤ y by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ y by nlinarith) (show (0 : ℝ) ≤ z by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ z by nlinarith) (show (0 : ℝ) ≤ x by nlinarith)]
    have h8 : y = z := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg (show (0 : ℝ) ≤ x by nlinarith) (show (0 : ℝ) ≤ y by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ y by nlinarith) (show (0 : ℝ) ≤ z by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ z by nlinarith) (show (0 : ℝ) ≤ x by nlinarith)]
    have h9 : x = 1 := by
      have h11 : x * (x - 1) ^ 2 = 0 := by
        have h14 : 2 * x ^ 2 = x * (1 + x ^ 2) := by
          have h15 : x = y := by
            linarith
          rw [show y = x by linarith] at h1'
          nlinarith
        nlinarith [sq_nonneg (x - 1)]
      cases (mul_eq_zero.1 h11) with
      | inl h =>
        exfalso
        apply hx
        linarith
      | inr h =>
        have h13 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h
        linarith
    have eq2 : y = 1 := by
      nlinarith
    have eq3 : z = 1 := by
      nlinarith
    right
    exact ⟨h9, eq2, eq3⟩