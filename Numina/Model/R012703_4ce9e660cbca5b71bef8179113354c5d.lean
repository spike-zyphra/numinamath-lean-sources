import Mathlib

theorem algebra_606109 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h₀ : f a = 1) (h₁ : ∀ x y, 0 < x → 0 < y → f x * f y + f (a / x) * f (a / y) = 2 * f (x * y)) :
    ∀ x, 0 < x → f x = 1 := by
  have h2 : f 1 = 1 := by
    specialize h₁ 1 1 (by linarith) (by linarith)
    simp at h₁
    nlinarith [h₀]

  have h3 : ∀ x, 0 < x → f (a / x) = f x := by
    intro x hx
    specialize h₁ x 1 (by linarith) (by linarith)
    simp [h2, h₀] at h₁
    linarith

  have h4 : ∀ x, 0 < x → (f x) ^ 2 = 1 := by
    intro x hx
    specialize h₁ x (a / x) (by linarith) (by positivity)
    have h5 : x * (a / x) = a := by
      field_simp [hx.ne']
      <;> nlinarith
      <;> field_simp [hx.ne']
      <;> nlinarith
    rw [h5] at h₁

    have h7 : f (a / x) = f x := h3 x hx
    rw [h7] at h₁

    have h8 : a / (a / x) = x := by
      field_simp [(show a ≠ 0 by linarith)]
      <;> nlinarith
      <;> field_simp [(show a ≠ 0 by linarith)]
      <;> nlinarith 
    have h9 : f (a / (a / x)) = f x := by
      rw [h8]

    rw [h9] at h₁
    nlinarith [h₀]

  intro x hx
  have h₅ := h₁ (√x) (√x) (by positivity) (by positivity)
  have h₆ : √x * √x = x := by
    rw [Real.mul_self_sqrt]
    linarith
  have h₇ : a / √x = a / √x := rfl
  have h₈ := h4 (√x) (by positivity)
  have h₉ := h4 x (show 0 < x by linarith)
  have h₁₀ := h3 (√x) (show 0 < √x by positivity)
  norm_num [h₆] at h₅
  norm_num [h₁₀] at h₅
  nlinarith [h₈, h₉, h₀, Real.sqrt_nonneg x]