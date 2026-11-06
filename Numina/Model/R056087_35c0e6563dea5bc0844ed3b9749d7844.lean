import Mathlib

theorem algebra_161517 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    (∀ x y, f (x + y) * f (x - y) = f x ^ 2 * f y ^ 2) ↔ ∀ y, f y = 0 := by
  constructor
  · -- Assume f satisfies the functional equation, and prove f(y) = 0 for all y
    intro h
    -- First, prove that f(0) = 0
    have h1 : f 0 = 0 := by
      have h00 := h 0 0
      simp at h00
      have h00' : (f 0) ^ 2 * (f 0 ^ 2 - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h00') with h2 h3
      · -- Case where f 0 = 0
        have h4 : f 0 = 0 := by
          simp at h2 ⊢
          nlinarith
        exact h4
      · -- Case where f 0 is either 1 or -1
        have h4 : f 0 ^ 2 = 1 := by linarith
        have h5 : f 0 = 1 ∨ f 0 = -1 := by
          rw [sq_eq_one_iff] at h4
          exact h4
        cases' h5 with h6 h7
        · -- Case where f 0 = 1
          exfalso
          have h8 : f 0 = -f 0 := by
            specialize hf 0
            norm_num at hf ⊢
            linarith
          linarith
        · -- Case where f 0 = -1
          exfalso
          have h8 : f 0 = -f 0 := by
            specialize hf 0
            norm_num at hf ⊢
            linarith
          linarith
    intro y
    have h2 := h y 0
    simp [h1] at h2
    have : f y = 0 := by
      nlinarith
    exact this
  · -- Conversely, if f(y) = 0 for all y, then it satisfies the functional equation
    intro h
    intro x y
    rw [h (x + y), h (x - y), h x, h y]
    all_goals norm_num