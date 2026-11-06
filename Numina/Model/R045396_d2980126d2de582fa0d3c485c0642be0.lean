import Mathlib

theorem algebra_314332 {a b c : ℝ} (h : a * b * c ≠ 0) (h1 : ∃ x, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧ c * x ^ 2 + a * x + b = 0) :
    a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = 3 := by
  rcases h1 with ⟨x, h1, h2, h3⟩
  have h4 : a + b + c = 0 := by
    have eq1 : a * x ^ 2 + b * x + c = 0 := h1
    have eq2 : b * x ^ 2 + c * x + a = 0 := h2
    have eq3 : c * x ^ 2 + a * x + b = 0 := h3
    have eq4 : a * x ^ 2 + b * x + c + b * x ^ 2 + c * x + a + c * x ^ 2 + a * x + b = 0 := by
      linarith [eq1, eq2, eq3]
    have eq5 : (a + b + c) * (x ^ 2 + x + 1) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    have hx : x ^ 2 + x + 1 ≠ 0 := by
      have h5 : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      linarith
    cases (mul_eq_zero.1 eq5) with
    | inl h5 =>
      linarith
    | inr h6 =>
      have h7 : x ^ 2 + x + 1 = 0 := h6
      have h8 : x ^ 2 + x + 1 ≠ 0 := hx
      contradiction

  have ha : a ≠ 0 := by
    by_contra h₁
    have h₂ : a * b * c = 0 := by
      rw [h₁]
      norm_num
    contradiction

  have hb : b ≠ 0 := by
    by_contra h₁
    have h₂ : a * b * c = 0 := by
      rw [h₁]
      norm_num
    contradiction

  have hc : c ≠ 0 := by
    by_contra h₁
    have h₂ : a * b * c = 0 := by
      rw [h₁]
      norm_num
    contradiction

  have h6 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by
    have h7 : c = -a - b := by linarith
    rw [h7]
    ring

  have h7 : a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by
    field_simp [hb, hc, ha]
    ring

  rw [h7]
  rw [h6]
  have h8 : a * b * c ≠ 0 := h
  field_simp [h8]