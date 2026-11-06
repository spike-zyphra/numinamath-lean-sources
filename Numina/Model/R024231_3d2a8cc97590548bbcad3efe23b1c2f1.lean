import Mathlib

theorem algebra_159902 {f : ℝ → ℝ} (hf : ∀ x y, f (x * y) * (x + f y) = x ^ 2 * f y + y ^ 2 * f x) :
    (∀ x, f x = 0) ∨ (∀ x, f x = x) := by

  have h1 : ∀ y, f 0 * (f y) = y ^ 2 * f 0 := by
    intro y
    specialize hf 0 y
    simp at hf
    linarith
  have h2 : f 0 = 0 := by
    have h3 := h1 0
    norm_num at h3
    nlinarith

  have h3 : f 1 ^ 2 = f 1 := by
    have h4 := hf 1 1
    norm_num at h4
    nlinarith

  have h4 : f 1 = 0 ∨ f 1 = 1 := by
    have h5 : f 1 * (f 1 - 1) = 0 := by linarith
    cases (mul_eq_zero.1 h5) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith

  cases h4 with
  | inl hf1 =>
    have h5 : ∀ x : ℝ, f x * (x - 1) = 0 := by
      intro x
      have h6 := hf x 1
      simp [hf1] at h6
      linarith
    left
    intro x
    have h6 : f x * (x - 1) = 0 := h5 x
    cases (mul_eq_zero.1 h6) with
    | inl h => 
      linarith
    | inr h => 
      have h7 : x = 1 := by linarith
      rw [h7]
      linarith
  | inr hf1 =>
    right
    intro x
    have h6 := hf x 1
    simp [hf1] at h6
    have eq1 : f x * x = x ^ 2 := by linarith
    by_cases h7 : x = 0
    · -- x = 0
      rw [h7]
      have h8 : f 0 = 0 := h2
      linarith
    · -- x ≠ 0
      have h8 : x ≠ 0 := by
        exact h7
      have h9 : f x = x := by
        apply (mul_left_inj' h8).mp
        linarith
      exact h9