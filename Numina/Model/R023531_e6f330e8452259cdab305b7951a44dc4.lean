import Mathlib

theorem algebra_254262 (f : ℝ → ℝ)
    (h₀ : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h₁ : ∀ x y, f (x * f y) * f y = f (x + y))
    (h₂ : f 2 = 0)
    (h₃ : ∀ x ∈ Set.Ioo 0 2, f x ≠ 0) :
    ∀ x, 0 ≤ x → f x = x := by 
  have h5 : f 0 = 1 := by 
    have eq1 := h₁ 0 1
    have h8 : f 1 ≠ 0 := by 
      apply h₃ 1
      norm_num 
    have eq2 : f (0 * f 1) * f 1 = f (0 + 1) := eq1 
    simp [show 0 * f 1 = (0 : ℝ) by nlinarith] at eq2 
    have eq3 : f 0 * f 1 = f 1 := by 
      linarith [eq2]
    have eq4 : f 0 * f 1 = f 1 := eq3 
    have h10 : f 1 ≠ 0 := h8 
    have eq5 : f 0 = 1 := by 
      apply (mul_left_inj' h10).mp 
      linarith [eq4]
    linarith

  have h11 : ∀ x ≥ (0 : ℝ), f (x + 2) = 0 := by 
    intro x hx 
    specialize h₁ x 2 
    simp [h₂] at h₁ 
    linarith

  have h13 := h₁ 1 1
  have h14 : f 1 ≠ 0 := by 
    apply h₃ 1 
    norm_num 
  have eq3 : f (1 * f 1) * f 1 = f (1 + 1) := by simpa using h13 
  have eq4 : f (1 * f 1) * f 1 = 0 := by
    rw [show (1 + 1 : ℝ) = (2 : ℝ) by norm_num, h₂] at eq3 
    linarith 
  have h15 : f (1 * f 1) = 0 := by
    have h16 : f 1 ≠ 0 := h14
    apply (mul_left_inj' h16).mp
    linarith [eq4]

  have h17 := h₁ (-f 1) (f 1)
  have eq5 : f ((-f 1) * f (f 1)) * f (f 1) = f ((-f 1) + f 1) := by simpa using h17 
  have h18 : f (f 1) = 0 := by 
    have eq6 : 1 * f 1 = (f 1 : ℝ) := by ring 
    rw [eq6] at h15 
    linarith 
  have eq6 : (-f 1) * f (f 1) = 0 := by 
    rw [h18] 
    norm_num 
  have eq8 : (-f 1 : ℝ) + f 1 = (0 : ℝ) := by 
    ring 
  rw [eq6, h18, eq8] at eq5 
  -- So f (0) * 0 = f (0) implies 0 = f (0).
  -- Now we have f (0) = 0.
  have eq9 : f (0) = 0 := by 
    nlinarith 
  linarith [h5, eq9]