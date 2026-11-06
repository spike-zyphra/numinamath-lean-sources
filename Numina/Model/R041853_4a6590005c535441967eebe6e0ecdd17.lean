import Mathlib

theorem algebra_285570 {p q r s : ℝ} (h : ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ x^2 + p * x + q = 0 ∧ y^2 + r * y + s = 0 ∧ x = 1 / y) :
    (p * s - r) * (q * r - p) = (q * s - 1)^2 := by
  rcases h with ⟨x, y, hx1, hy1, h1, h2, h3⟩
  have h4 : y = 1 / x := by 
    field_simp [show y ≠ 0 by assumption, show x ≠ 0 by assumption] at h3 ⊢
    all_goals linarith
  have eq3 : (1 / x) ^ 2 + r * (1 / x) + s = 0 := by
    rw [h4] at h2
    linarith
  have eq4 : s * x^2 + r * x + 1 = 0 := by
    have hx4' : x ≠ 0 := hx1
    have eq3' : (1 / x) ^ 2 + r * (1 / x) + s = 0 := by linarith [eq3]
    have eq7 : s * x ^ 2 + r * x + 1 = 0 := by
      have hx5' : x ≠ 0 := hx4'
      have eq8 : (1 / x) ^ 2 + r * (1 / x) + s = 0 := eq3'
      have eq9 : (1 / x) ^ 2 + r * (1 / x) + s = (1 + r * x + s * x ^ 2) / x ^ 2 := by
        field_simp [hx5']
        <;> ring
      rw [eq9] at eq8
      have hne : x ^ 2 ≠ 0 := by
        apply pow_ne_zero
        exact hx5'
      have eq10 : 1 + r * x + s * x ^ 2 = 0 := by
        field_simp [hne] at eq8 ⊢
        <;> linarith
      linarith [eq10]
    linarith [eq7]
  have eq1 : x ^ 2 + p * x + q = 0 := h1
  have eq5' : (p * s - r) * (q * r - p) = (q * s - 1) ^ 2 := by
    have eq6 : q = -x^2 - p * x := by linarith [eq1]
    have eq7 : s = (-1 - r * x) / x^2 := by
      have hx8 : x ≠ 0 := hx1
      have hx9 : x^2 ≠ 0 := by
        intro h
        apply hx1
        nlinarith
      field_simp [hx8, hx9] at eq4 ⊢
      linarith [eq4]
    rw [eq6]
    have hx8 : x ≠ 0 := hx1
    simp only [eq7]
    have hx2 : x ≠ 0 := hx1
    field_simp [show x ≠ 0 by assumption, show x^2 ≠ 0 by
      intro h
      apply hx1
      nlinarith 
    ]
    <;> nlinarith [sq_nonneg (x^2), sq_nonneg (x + p), sq_nonneg (x * r + p * r), sq_nonneg (x * p + r * x), sq_pos_of_ne_zero (show x^2 ≠ 0 by intro h; apply hx1; nlinarith), sq_nonneg (p + r * x), sq_nonneg (p * x + r * x^2), sq_nonneg (x * r), sq_nonneg ((x ^ 2) * (p + r * x)), sq_nonneg (p * (p + r * x)), sq_nonneg ((x ^ 2) * (p + r * x)^2), sq_nonneg ((p * (p + r * x)) * (x ^ 2))]
  assumption