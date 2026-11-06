import Mathlib
theorem algebra_607257 (f : ℝ → ℝ) : (∀ x y, f x * f y = f (x * y) + x + y) ↔ ∀ x, f x = 1 + x := by 
  constructor
  · -- First, we show that ∀ x, f x = 1 + x given the functional equation.
    intro h
    have h1 : f 0 = 0 ∨ f 0 = 1 := by
      have h0 := h 0 0
      simp at h0
      have : f 0 * (f 0 - 1) = 0 := by linarith
      cases (mul_eq_zero.mp this) with
      | inl h2 => 
        left; linarith
      | inr h2 => 
        right; linarith
    cases h1 with
    | inl h0_eq_0 =>
      have h2 := h 1 0
      norm_num [h0_eq_0] at h2
      all_goals try linarith
      all_goals try { exfalso <;> linarith }
    | inr h0_eq_1 =>
      intro x
      have h2 := h x 0
      rw [h0_eq_1] at h2
      simp at h2 
      nlinarith 
  · -- Now, we prove the converse: if f(x) = 1 + x for all x, then the functional equation holds.
    intro hf x y
    have h1 : f x = 1 + x := hf x
    have h2 : f y = 1 + y := hf y
    have h3 : f (x * y) = 1 + (x * y) := hf (x * y)
    rw [h1, h2, h3]
    ring