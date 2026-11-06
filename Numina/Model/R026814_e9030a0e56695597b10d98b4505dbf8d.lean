import Mathlib


theorem algebra_222029 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h₀ : f a = 1) (h₁ : ∀ x y : ℝ, 0 < x → 0 < y → f x * f y + f (a / x) * f (a / y) = 2 * f (x * y)) :
    ∃ c, ∀ x : ℝ, 0 < x → f x = c := by

  have h2 : f 1 = 1 := by
    have eq1 := h₁ a 1 (by linarith) (by linarith)
    simp [show a / a = 1 by field_simp, h₀] at eq1
    nlinarith

  have h3 : ∀ x : ℝ, 0 < x → f (a / x) = f x := by
    intro x hx
    have eq1 := h₁ x 1 hx (by linarith)
    simp [h2, h₀] at eq1
    linarith

  have h4 : ∀ x : ℝ, 0 < x → (f x) ^ 2 = 1 := by
    intro x hx
    have eq1 := h₁ x (a / x) hx (show 0 < a / x by positivity)
    have eq2 : f (a / (a / x)) = f x := by
      have eq3 : a / (a / x) = x := by
        field_simp
      rw [eq3]
    have eq3 : f (a / x) = f x := by
      apply h3
      positivity
    simp [eq3, eq2, show x * (a / x) = a by
      field_simp
    ] at eq1
    nlinarith [h₀]

  use 1
  intro x hx
  have h5 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.mpr
    linarith
  have h6 : Real.sqrt x * Real.sqrt x = x := by
    calc
      Real.sqrt x * Real.sqrt x = (Real.sqrt x) ^ 2 := by ring
      _ = x := by
        rw [Real.sq_sqrt]
        linarith
  have eq1 := h₁ (Real.sqrt x) (Real.sqrt x) (by positivity) (by positivity)
  have eq2 : f (Real.sqrt x) ^ 2 = 1 := by
    apply h4
    positivity
  have eq3 : f (a / Real.sqrt x) ^ 2 = 1 := by
    apply h4
    positivity
  have eq4 : f (Real.sqrt x * Real.sqrt x) = 1 := by
    have eq5 : f (Real.sqrt x) ^ 2 = 1 := eq2
    have eq6 : f (a / Real.sqrt x) ^ 2 = 1 := eq3
    have eq7 : f (Real.sqrt x) * f (Real.sqrt x) + f (a / Real.sqrt x) * f (a / Real.sqrt x) = 2 * f (Real.sqrt x * Real.sqrt x) := by
      simpa using eq1
    nlinarith
  rw [h6] at eq4
  linarith