import Mathlib

theorem algebra_4687 (f : ℕ → ℕ) : (∀ x y, (x * f y + y * f x) ^ (x + y) = f x * f y * (x + y) ^ (x + y)) ↔
    ∀ x, f x = 1 := by 
  constructor
  · -- First direction: if f satisfies the equation, then f(x) = 1 for all x.
    intro h
    have h0 : f 0 = 1 := by
      specialize h 0 0
      simp at h
      nlinarith
    have h1 : f 1 = 1 := by
      specialize h 1 0
      simp [h0] at h
      linarith
    intro x 
    induction x with 
    | zero =>
      exact h0 
    | succ x ih =>
      have h2 := h (x + 1) 0 
      simp [h0] at h2
      all_goals
      have h4 : f (x + 1) = 1 := by
        nlinarith
      simpa using h4
  · -- Backward direction: if f(x) = 1 for all x, then it satisfies the equation
    intro h x y
    have hx : f x = 1 := h x
    have hy : f y = 1 := h y 
    rw [hx, hy]
    all_goals 
      ring_nf