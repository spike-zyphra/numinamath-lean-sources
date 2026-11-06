import Mathlib

theorem algebra_104059 (f : ℝ → ℝ) :
    (∀ x y z, f (x * y * z) = f x * f y * f z - 6 * x * y * z) ↔ ∀ x, f x = 2 * x := by
  constructor
  · -- Assume the functional equation holds: define an operation
    intro h 
    have h1 : ∀ x, f (x) = 2 * x := by 
      -- Show f 1 = 2 
      have h_eq : f 1 = 2 := by
        have eq1 := h 1 1 1
        norm_num at eq1
        have eq2 : f 1 ^ 3 - f 1 - 6 = 0 := by
          linarith
        -- Solving the cubic equation
        have eq3 : (f 1 - 2) * (f 1 ^ 2 + 2 * f 1 + 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 eq3) with h2 h3
        · -- Case f 1 - 2 = 0
          linarith
        · -- Case f 1 ^ 2 + 2 * f 1 + 3 = 0
          nlinarith [sq_nonneg (f 1 + 1)]
      intro x
      have eq2 := h x 1 1
      simp [h_eq] at eq2
      linarith
    intro x
    apply h1 x 
  · -- Assume f is known, prove the functional equation
    intro h x y z 
    rw [h (x * y * z), h x, h y, h z]
    ring_nf