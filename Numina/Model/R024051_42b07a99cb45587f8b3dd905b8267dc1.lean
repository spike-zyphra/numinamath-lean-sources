import Mathlib

theorem algebra_303567 {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h₀ : ∀ x, f 1 x = a * x + b)
    (h₁ : ∀ n ≥ 1, f (n + 1) = f 1 ∘ f n)
    (h₂ : ∀ x, f 7 x = 128 * x + 381) :
    a + b = 5 := by
  -- Prove $f_7(x)$ expression
  have f7 : ∀ x, f 7 x = a^7 * x + b * (1 + a + a^2 + a^3 + a^4 + a^5 + a^6) := by 
    have eq1 : f 7 = f 1 ∘ f 6 := by
      have h1 := h₁ 6 (by norm_num)
      simpa using h1
    have eq2 : f 6 = f 1 ∘ f 5 := by 
      have h2 := h₁ 5 (by norm_num)
      simpa using h2
    have eq3 : f 5 = f 1 ∘ f 4 := by 
      have h3 := h₁ 4 (by norm_num)
      simpa using h3
    have eq4 : f 4 = f 1 ∘ f 3 := by 
      have h4 := h₁ 3 (by norm_num)
      simpa using h4
    have eq5 : f 3 = f 1 ∘ f 2 := by 
      have h5 := h₁ 2 (by norm_num)
      simpa using h5
    have eq6 : f 2 = f 1 ∘ f 1 := by 
      have h6 := h₁ 1 (by norm_num)
      simpa using h6
    intro x
    simp [eq1, eq2, eq3, eq4, eq5, eq6, Function.comp_apply, h₀]
    <;> ring_nf 
    <;> simp [h₀] <;> ring_nf <;> simp [h₀] <;> ring_nf 
    all_goals try linarith
  have eq1 := h₂ 0
  simp [f7] at eq1 
  have eq2 := h₂ 1
  simp [f7] at eq2 
  have ha : a^7 = 128 := by 
    nlinarith 
  have ha2 : a = 2 := by 
    have ha_eq : a^7 - 128 = 0 := by linarith 
    have ha_eq2 : a^7 - 128 = (a - 2) * (a^6 + 2*a^5 + 4*a^4 + 8*a^3 + 16*a^2 + 32*a + 64) := by ring
    rw [ha_eq2] at ha_eq
    cases' (mul_eq_zero.mp ha_eq) with ha2' ha_eq3
    · -- a - 2 = 0
      linarith 
    · -- a^6 + ... = 0
      nlinarith [sq_nonneg (a^3 + 2 * a^2 + 4 * a + 8), sq_nonneg (a^2 + a + 1), sq_nonneg (a + 2), sq_nonneg (a * 2 - 2)]
  have hb : b = 3 := by 
    rw [ha2] at eq1 
    norm_num at eq1 
    linarith 
  linarith [ha2, hb]