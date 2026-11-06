import Mathlib

theorem algebra_210119 {x y : ℝ} (hx : x^2 + y^2 ≠ 0) (hxy : x + (x + 2 * y) / (x ^ 2 + y ^ 2) = 2 ∧ y + (2 * x - y) / (x ^ 2 + y ^ 2) = 0) :
    (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = -1) := by
  rcases hxy with ⟨h1, h2⟩
  have eq1 : x + 2 * y = (2 - x) * (x^2 + y^2) := by
    have h11 : x ^ 2 + y ^ 2 ≠ 0 := hx
    field_simp [h11] at h1 ⊢
    nlinarith
  have eq2 : 2 * x - y = -y * (x^2 + y^2) := by
    have h11 : x ^ 2 + y ^ 2 ≠ 0 := hx
    field_simp [h11] at h2 ⊢
    nlinarith
  have h3 : (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = -1) := by
    have eq3 : (x - 0) * (x - 2) = 0 := by
      nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 1), sq_nonneg (x - 2), sq_nonneg (y + 1), 
        sq_pos_of_ne_zero hx]
    cases (mul_eq_zero.1 eq3) with
    | inl h4 =>
      have hx0 : x = 0 := by linarith
      have eq4 : y = 0 ∨ y = 1 := by
        rw [hx0] at eq1
        have : y * (y - 1) = 0 := by 
          nlinarith
        cases (mul_eq_zero.1 this) with
        | inl h5 => 
          left; linarith
        | inr h6 => 
          right; linarith
      cases eq4 with
      | inl hy0 =>
        have h4 : x^2 + y^2 = 0 := by
          rw [hx0, hy0]
          norm_num
        contradiction
      | inr hy1 =>
        left; constructor <;> linarith
    | inr h4 =>
      have hx2 : x = 2 := by linarith
      have hy1 : y = -1 := by
        rw [hx2] at eq1
        nlinarith
      right; constructor <;> linarith
  assumption