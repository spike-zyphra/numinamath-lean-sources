import Mathlib

theorem algebra_8130 {f : ℝ → ℝ} : (∀ x y, f x * f y + 1 = f x + f y + x * y) ↔
    (∀ x, f x = 1 + x) ∨ (∀ x, f x = 1 - x) := by 
  constructor 
  · -- Assume the functional equation holds, prove the solutions 
    intro h 
    have h1 : f 0 = 1 := by 
      have h00 := h 0 0 
      simp at h00 
      have h1 : (f 0 - 1) ^ 2 = 0 := by 
        nlinarith 
      have h2 : f 0 - 1 = 0 := by 
        apply pow_eq_zero 
        exact h1 
      linarith 
    have h2 : ∀ x, (f x - 1) ^ 2 = x ^ 2 := by 
      intro x 
      have hx : f x * f x + 1 = f x + f x + x * x := by 
        specialize h x x 
        simpa using h 
      nlinarith 
    have h3 : ∀ x, f x = 1 + x ∨ f x = 1 - x := by 
      intro x 
      have h1x : (f x - 1) ^ 2 = x ^ 2 := h2 x 
      have : f x - 1 = x ∨ f x - 1 = -x := by 
        have h1x' : (f x - 1) ^ 2 - x ^ 2 = 0 := by linarith 
        have h2x' : (f x - 1 - x) * (f x - 1 + x) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h2x') with h4 h5 
        · left 
          linarith 
        · right 
          linarith 
      cases' this with h4 h5 
      · left 
        linarith 
      · right 
        linarith 
    have eq1 := h3 1 
    cases eq1 with
    | inl h4 =>
      -- Assume f 1 = 2.
      have h41 : f 1 = 2 := by 
        linarith 
      -- Show that it satisfies f x = 1 + x
      left 
      intro y 
      have hy1 := h 1 y 
      simp [h41] at hy1 
      linarith 
    | inr h4 =>
      -- Assume f 1 = 0.
      have h41 : f 1 = 0 := by 
        linarith 
      -- Show that f x = 1 - x.
      right 
      intro x 
      have hx1 := h 1 x 
      simp [h41] at hx1 
      linarith 
  · -- Show the solutions satisfy the functional equation.
    rintro (h | h)
    · -- Assume ∀ x, f x = 1 + x 
      intro x y 
      rw [h x, h y] 
      ring 
    · -- Assume ∀ x, f x = 1 - x 
      intro x y 
      rw [h x, h y] 
      ring