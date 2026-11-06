import Mathlib

theorem algebra_294090 (f : ℝ → ℝ) :
    (∀ x y, f x * f y = f (x * y) + x + y) ↔ ∀ x, f x = 1 + x := by
  constructor
  · -- Assume ∀ x y, f x * f y = f (x * y) + x + y, prove ∀ x, f x = 1 + x
    intro h_eq
    have h00 : f 0 * f 0 = f (0 * 0) + (0 : ℝ) + (0 : ℝ) := h_eq 0 0
    simp at h00
    -- From f(0)*f(0) = f(0), so f(0)^2 = f(0), which implies f(0) = 0 or f(0) = 1.

    have h11 : f 1 * f 1 = f (1 * 1) + (1 : ℝ) + (1 : ℝ) := h_eq 1 1
    simp at h11
    -- From f(1)*f(1) = f(1) + 2, we get quadratic equation f(1)^2 - f(1) - 2 = 0, solutions f(1) = 2 or f(1) = -1.
  
    have h10 : f 1 * f 0 = f (1 * 0) + (1 : ℝ) + (0 : ℝ) := h_eq 1 0
    norm_num at h10
    -- Substituting (1,0): f(1)*f(0) = f(0) + 1 + 0, which simplifies to f(1)*f(0) = f(0) + 1.
  
    have h3 : f 0 * (f 1 - 1) = 1 := by
      nlinarith -- Algebraic manipulation to convert f(1)*f(0) = f(0) + 1 into f(0)*(f(1) - 1) = 1
  
    have h4 : f 0 * (f 0 - 1) = 0 := by
      nlinarith -- From h00: f(0)^2 = f(0), so f(0)* (f(0) - 1) = 0.

    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case h5: f 0 = 0
      have h5' : f 0 = 0 := by
        linarith

      rw [h5'] at h3
      all_goals
      nlinarith
  
    · -- Case h6: f 0 - 1 = 0  so f 0 = 1
      have h5' : f 0 = 1 := by
        nlinarith
  
      have h5_1 : f 1 = 2 := by
        rw [h5'] at h3
        nlinarith
  
      intro x
      have h56 := h_eq x 1
      simp [h5_1] at h56
  
      -- Substituting (x,1): f(x) * f(1) = f(x) + x + 1
      -- Since f(1) = 2, we get 2*f(x) = f(x) + x + 1
      -- Simplifies to f(x) = x + 1, which is the desired result
      have h57 : f x = 1 + x := by
        nlinarith -- Linear arithmetic to solve the equation
  
      exact h57
  
  · -- Assume ∀ x, f x = 1 + x, prove ∀ x y, f x * f y = f (x * y) + x + y
    intro h x y
    have hx := h x
    have hy := h y
    have hxy := h (x * y)
  
    -- Substituting f(x) = 1+x, f(y) = 1+y, and f(x*y) = 1+x*y into the left side:
    -- Left: (1+x)*(1+y) = 1 + y + x + x*y
    -- Right: (1 + x*y) + x + y = 1 + x*y + x + y
    rw [hx, hy, hxy]
    ring -- Algebraic manipulations show left = right