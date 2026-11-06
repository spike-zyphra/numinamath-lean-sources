import Mathlib

theorem algebra_604558{f: ℝ → ℝ}:
  ( ∀(x y: ℝ), (f x)*(f y) = f (x*y) + x + y ) ↔
  ( ∀x, f x = x + 1) := by
  constructor
  · -- assuming left side, proving right side
    intro h
    -- first, we work on f(0). by set x=y=0, we find f(0) = 0 ∨ f(0) = 1
    have h1 : f 0 = 1 := by
      have h0 := h 0 0
      simp at h0
      have h2 := h 1 0
      simp at h2
      have h4 : f 0 * (f 0 - 1) = 0 := by linarith 
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- h5: f 0 = 0 
        have h7 : f 0 = 0 := by linarith
        rw [h7] at h2
        all_goals nlinarith
      · -- h6: f 0 - 1 = 0 
        linarith
    -- next, we can find f(1) from h1
    have h2' : f 1 = 2 := by
      have h1_val : f 0 = 1 := h1
      specialize h 1 0
      simp [h1_val] at h
      linarith
    -- then, we set y = 0 in h, and we get f(x) = x + 1 for all x
    intro x
    have h2 := h x 0
    simp [h1] at h2
    linarith
  · -- the other direction
    intro h x y
    rw [h x, h y, h (x * y)]
    ring