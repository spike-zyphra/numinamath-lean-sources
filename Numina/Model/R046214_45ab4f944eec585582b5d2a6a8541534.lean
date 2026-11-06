import Mathlib


theorem algebra_166276 {x y : ℝ} (hxy : x ≠ 0 ∧ y ≠ 0) (h1 : x * y - x / y = 16 / 3) (h2 : x * y - y / x = 9 / 2) :
    (x = 2 ∧ y = 3) ∨ (x = -2 ∧ y = -3) := by
  rcases hxy with ⟨hx, hy⟩
  have eq1 : x / y = x * y - 16 / 3 := by
    have h1' : x * y - x / y = 16 / 3 := h1
    linarith
  have eq2 : y / x = x * y - 9 / 2 := by
    have h2' : x * y - y / x = 9 / 2 := h2
    linarith
  have eq3 : (x / y) * (y / x) = 1 := by
    field_simp [hx, hy]
  have eq4 : (x * y - 16 / 3) * (x * y - 9 / 2) = 1 := by
    rw [eq1, eq2] at eq3
    nlinarith
  have h3 : 6 * (x * y)^2 - 59 * (x * y) + 138 = 0 := by
    nlinarith [eq4]
  have h4 : (x * y - 6) * (x * y - 23 / 6) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- case $x * y = 6$
    have h7 : x * y = 6 := by linarith
    have eq7 : x / y = 2 / 3 := by
      nlinarith [eq1, h7]
    have eq8 : x = 2 / 3 * y := by
      have h11 : y ≠ 0 := hy
      field_simp [h11] at eq7 ⊢
      linarith
    rw [eq8] at h7
    have h8 : y ^ 2 = 9 := by
      nlinarith
    have h9 : y = 3 ∨ y = -3 := by
      have h10 : y ^ 2 - 9 = 0 := by linarith
      have h11 : (y - 3) * (y + 3) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h11) with h12 h13
      · left
        linarith
      · right
        linarith
    cases h9 with
    | inl hy3 =>
      have hx2 : x = 2 := by
        linarith [eq8, hy3]
      left
      exact ⟨hx2, hy3⟩
    | inr hy3 =>
      have hx2 : x = -2 := by
        linarith [eq8, hy3]
      right
      exact ⟨hx2, hy3⟩
  · -- case $x * y = 23/6$
    have h7 : x * y = 23 / 6 := by linarith
    have eq7 : x / y = -3 / 2 := by
      nlinarith [eq1, h7]
    have eq8 : x = -3 / 2 * y := by
      have h11 : y ≠ 0 := hy
      field_simp [h11] at eq7 ⊢
      linarith
    rw [eq8] at h7
    nlinarith [sq_nonneg (y), sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]