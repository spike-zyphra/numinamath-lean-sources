import Mathlib

theorem algebra_314421 {f : ℤ → ℝ} (h : ∀ x y, f (x + y) * f (x - y) = f x + f y) :
    f 2011 = 0 ∨ f 2011 = 2 ∨ f 2011 = -1 := by
  have h1 := h 0 0
  have h2 : f 0 * (f 0 - 2) = 0 := by
    norm_num at h1
    linarith 
  have h00 : f 0 = 0 ∨ f 0 = 2 := by 
    cases (mul_eq_zero.mp h2) with
    | inl h3 => 
      left
      linarith 
    | inr h4 => 
      right
      linarith 
  cases h00 with
  | inl h00 =>
    have h3 := h 2011 2011
    have eq3 : (2011 : ℤ) + (2011 : ℤ) = (4022 : ℤ) := by norm_num
    have eq4 : (2011 : ℤ) - (2011 : ℤ) = (0 : ℤ) := by norm_num
    rw [eq3, eq4] at h3 
    rw [h00] at h3
    have h2011_00 : f 2011 = 0 := by
      nlinarith 
    left 
    linarith [h2011_00]
  | inr h00 =>
    have h2011_00 := h 2011 0
    have eq3 : (2011 : ℤ) + (0 : ℤ) = (2011 : ℤ) := by norm_num
    have eq4 : (2011 : ℤ) - (0 : ℤ) = (2011 : ℤ) := by norm_num
    rw [eq3, eq4] at h2011_00
    have h2011_eq : f 2011 ^ 2 - f 2011 - 2 = 0 := by 
      rw [h00] at h2011_00 
      nlinarith 
    have h2011_or : f 2011 = 2 ∨ f 2011 = -1 := by
      have h2011_eq2 : f 2011 ^ 2 - f 2011 - 2 = 0 := h2011_eq
      have h2 : f 2011 ^ 2 - f 2011 - 2 = (f 2011 - 2) * (f 2011 + 1) := by 
        ring 
      rw [h2] at h2011_eq2 
      cases (mul_eq_zero.mp h2011_eq2) with
      | inl h3 => 
        left 
        linarith 
      | inr h4 => 
        right 
        linarith 
    cases h2011_or with
    | inl h2011_eq2 => 
      right 
      left 
      linarith 
    | inr h2011_eq3 => 
      right 
      right 
      linarith 
  all_goals try { linarith }
  all_goals try { tauto }