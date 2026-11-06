import Mathlib

theorem algebra_166575 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : Real.sqrt ((x / y) + 2 + (y / x)) = 5 / 2) (h2 : abs (x + y) = 5) :
    (x = -4 ∧ y = -1) ∨ (x = -1 ∧ y = -4) ∨ (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) := by

  have h1' : (x / y) + 2 + (y / x) ≥ 0 := by
    by_contra h
    push_neg at h
    have h3 : Real.sqrt ((x / y) + 2 + (y / x)) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
    rw [h3] at h1
    nlinarith

  have h_eq1 : (x / y) + 2 + (y / x) = 25 / 4 := by
    calc
      (x / y) + 2 + (y / x) = (Real.sqrt ((x / y) + 2 + (y / x)) ) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [h1']
      _ = (5 / 2) ^ 2 := by 
        rw [h1]
      _ = (25 / 4) := by
        norm_num

  have eq1 : (x / y) + (y / x) = 17 / 4 := by
    have eq2 : (x / y) + 2 + (y / x) = 25 / 4 := h_eq1
    linarith

  have eq2 : x ^ 2 + y ^ 2 = (17 / 4) * (x * y) := by
    have eq3 : (x / y) + (y / x) = 17 / 4 := eq1
    have eq4 : x / y + y / x = (x ^ 2 + y ^ 2) / (x * y) := by
      field_simp [hx, hy]
      <;> ring
    rw [eq4] at eq3
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    field_simp [hxy] at eq3 ⊢
    <;> nlinarith

  have h3 : x + y = 5 ∨ x + y = -5 := by
    cases eq_or_eq_neg_of_abs_eq h2 with
    | inl h4 =>
      left
      linarith
    | inr h4 =>
      right
      linarith

  cases h3 with
  | inl h4 =>
    have h5 : x + y = 5 := h4
    have h7 : x * y = 4 := by
      have eq3 : x ^ 2 + y ^ 2 = (17 / 4) * (x * y) := eq2
      have eq4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
        nlinarith
      rw [eq4, h5] at eq3
      nlinarith
    have h8 : (x - 1) * (x - 4) = 0 := by
      have h9 : y = 5 - x := by
        linarith
      rw [h9] at h7
      nlinarith
    cases (mul_eq_zero.mp h8) with
    | inl h9 =>
      have hx1 : x = 1 := by linarith
      have hy1 : y = 4 := by linarith
      right
      right
      left
      constructor <;> linarith
    | inr h9 =>
      have hx4 : x = 4 := by linarith
      have hy1 : y = 1 := by linarith
      right
      right
      right
      constructor <;> linarith
  | inr h4 =>
    have h5 : x + y = -5 := h4
    have h7 : x * y = 4 := by
      have eq3 : x ^ 2 + y ^ 2 = (17 / 4) * (x * y) := eq2
      have eq4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
        nlinarith
      rw [eq4, h5] at eq3
      nlinarith
    have h8 : (x + 1) * (x + 4) = 0 := by
      have h9 : y = -5 - x := by
        linarith
      rw [h9] at h7
      nlinarith
    cases (mul_eq_zero.mp h8) with
    | inl h9 =>
      have hx1 : x = -1 := by linarith
      have hy1 : y = -4 := by linarith
      right
      left
      constructor <;> linarith
    | inr h9 =>
      have hx4 : x = -4 := by linarith
      have hy1 : y = -1 := by linarith
      left
      constructor <;> linarith