import Mathlib

theorem algebra_306970 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 1 / a + 1 / b = 5 / 12)
    (h₂ : 1 / b + 1 / c = 4 / 16)
    (h₃ : 1 / a + 1 / c = 7 / 24)
    (h₄ : 180000 / a + 150000 / b + 160000 / c = 177000) :
    min (min (180000 / a) (150000 / b)) (160000 / c) = 177000 := by 
  rcases h₀ with ⟨ha, hb, hc⟩
  have h1' : a ≠ 0 := by linarith
  have h2' : b ≠ 0 := by linarith
  have h3' : c ≠ 0 := by linarith
  have eq1 : b + a = 5 / 12 * a * b := by 
    have h1 : a ≠ 0 := h1'
    have h2 : b ≠ 0 := h2'
    field_simp at h₁ ⊢
    linarith
  have eq2 : b + c = 1 / 4 * b * c := by 
    have h1 : b ≠ 0 := h2'
    have h2 : c ≠ 0 := h3'
    field_simp at h₂ ⊢
    linarith
  have eq3 : a + c = 7 / 24 * a * c := by 
    have h1 : a ≠ 0 := h1'
    have h2 : c ≠ 0 := h3'
    field_simp at h₃ ⊢
    linarith
  have eq5 : 180000 * b * c + 150000 * a * c + 160000 * a * b = 177000 * a * b * c := by
    have h1 : a ≠ 0 := h1'
    have h2 : b ≠ 0 := h2'
    have h3 : c ≠ 0 := h3'
    have eq5 : 180000 / a + 150000 / b + 160000 / c = 177000 := h₄
    have h5 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact h1
      exact h2
      exact h3
    have eq6 : (180000 / a + 150000 / b + 160000 / c) * (a * b * c) = 177000 * (a * b * c) := by
      rw [eq5]
    have eq7 : (180000 / a + 150000 / b + 160000 / c) * (a * b * c) = 180000 * b * c + 150000 * a * c + 160000 * a * b := by
      field_simp [h1', h2', h3']
      <;> ring
    rw [eq7] at eq6
    linarith
  nlinarith [sq_nonneg (a * b - 48), sq_nonneg (b * c - 96), sq_nonneg (a * c - 32), 
          sq_nonneg (a - 4), sq_nonneg (b - 6), sq_nonneg (c - 8),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]