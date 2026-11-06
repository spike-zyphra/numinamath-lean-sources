import Mathlib

theorem algebra_236099 (f g : ℝ → ℝ)
    (hf : f = fun x => 1 - x - 4 * x ^ 2 + x ^ 4)
    (hg : g = fun x => 16 - 8 * x - 16 * x ^ 2 + x ^ 4)
    (x₁ x₂ : ℝ)
    (hx₁ : f x₁ = 0) (hx₂ : g x₂ = 0)
    (hxp : ∀ x, f x = 0 → x ≤ x₁) (hxp' : ∀ x, g x = 0 → x ≤ x₂) :
    x₂ / x₁ = 2 := by
  have h1 : f x₁ = 0 := hx₁
  have h2 : g x₂ = 0 := hx₂

  have h3 : g (2 * x₁) = 0 := by
    have h4 : f x₁ = 0 := hx₁
    have h5 : g (2 * x₁) = 16 * f x₁ := by
      rw [hg, hf]
      ring_nf
      <;> nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg ((2 * x₁) ^ 2)]
    rw [h4] at h5
    linarith
  have h4 : 2 * x₁ ≤ x₂ := by
    have h5 : g (2 * x₁) = 0 := h3
    have h6 : 2 * x₁ ≤ x₂ := by
      apply hxp' (2 * x₁) h5
    linarith

  have eq3 : f (x₂ / 2) = 0 := by
    have h8 : g x₂ = 16 * f (x₂ / 2) := by
      rw [hg, hf]
      ring_nf
      <;> nlinarith [sq_nonneg (x₂ ^ 2), sq_nonneg (x₁ ^ 2), sq_nonneg ((x₂ / 2) ^ 2), sq_nonneg ((x₁) ^ 2), sq_nonneg (x₂ ^ 2 - 4 * x₁ ^ 2), sq_nonneg (x₂ - 2 * x₁), sq_nonneg (x₁ ^ 2 - (x₂ / 2) ^ 2), sq_nonneg ((x₁ - x₂ / 2) * (x₁ - x₂ / 2)), sq_nonneg ((x₂ - 2 * x₁) * (x₂ - 2 * x₁)), sq_nonneg (x₁ * (x₂ / 2)), sq_nonneg ((x₂ / 2) * x₁), sq_nonneg (x₂ / 2 * 2 * x₁), sq_nonneg (x₁ * (x₂ / 2) * (x₂ / 2)), sq_nonneg ((x₂ - 2 * x₁) * 2 * x₁)]
    rw [h8] at hx₂
    linarith 
  have h6 : x₂ / 2 ≤ x₁ := by
    have h7 : f (x₂ / 2) = 0 := eq3
    have h8 : x₂ / 2 ≤ x₁ := by
      apply hxp (x₂ / 2) h7
      all_goals linarith
    linarith

  have h7 : x₁ ≠ 0 := by
    by_contra h
    rw [h] at hx₁
    norm_num [hf] at hx₁
    all_goals nlinarith
  
  have h8 : x₂ = 2 * x₁ := by
    linarith [h4, h6]

  have h9 : x₂ / x₁ = 2 := by
    rw [h8]
    field_simp [h7]
    <;> nlinarith
  
  exact h9