import Mathlib

theorem algebra_13153 {f : ℝ → ℝ} (h : ∀ x y, (f x * f y - f (x * y)) / 3 = x + y + 2) :
    ∀ x, f x = x + 3 := by

  have h1 : f 0 = 3 ∨ f 0 = -2 := by
    have h2 := h 0 0
    norm_num at h2
    have h3 : f 0 ^ 2 - f 0 - 6 = 0 := by
      nlinarith
    have h4 : (f 0 - 3) * (f 0 + 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h4) with
    | inl h5 =>
      left
      linarith
    | inr h6 =>
      right
      linarith

  intro x 
  have h2 : (f x * f 0 - f (x * (0 : ℝ))) / 3 = x + (0 : ℝ) + 2 := h x 0
  simp at h2 
  have eq1 : f x * f 0 - f 0 = 3 * x + 6 := by 
    linarith 
  cases h1 with
  | inl h1' =>
    rw [h1'] at eq1 
    nlinarith
  | inr h1' =>
    exfalso
    have eq31 : f 1 * f 0 - f 0 = 3 * (1 : ℝ) + 6 := by 
      have h11 := h 1 0 
      norm_num at h11 ⊢ 
      linarith 
    have eq31' : f 1 * (-2) + 2 = 9 := by
      rw [h1'] at eq31
      nlinarith
    have eq32 : f 1 = (-7 / 2 : ℝ) := by 
      nlinarith [eq31']

    have eq33 : (f 1 * f 1 - f (1 * (1 : ℝ))) / 3 = (1 + (1 : ℝ) + 2) := by
      specialize h 1 1
      simpa using h 
    have eq34 : f (1 * (1 : ℝ)) = f 1 := by 
      ring_nf 
    rw [eq34] at eq33 
    have eq35 : f 1 * f 1 - f 1 = 12 := by 
      nlinarith 
    rw [eq32] at eq35 
    norm_num at eq35