import Mathlib

theorem algebra_16436 {f : ℝ → ℝ} (h : ∀ x y, f (x - y) = f x * f y) (h' : ∀ x, f x ≠ 0) :
    f 3 = 1 := by

  have h1 : f 0 = 1 := by
    have h00 : f (0 - (0 : ℝ)) = f 0 * f 0 := by
      apply h
    have eq1 : f 0 = f 0 * f 0 := by
      simpa using h00
    have eq2 : f 0 * (1 - f 0) = 0 := by
      linarith
    cases' (mul_eq_zero.mp eq2) with h2 h3
    · -- Case f 0 = 0
      have h0 : f 0 = 0 := by
        linarith
      have h00 : f 0 ≠ 0 := by
        apply h'
      contradiction
    · -- Case 1 - f 0 = 0
      linarith
  have h2 : f (3 - (3 / 2 : ℝ)) = f 3 * f (3 / 2 : ℝ) := by
    apply h
  have eq3 : f (3 - (3 / 2 : ℝ)) = f (3 / 2 : ℝ) := by
    ring_nf
  rw [eq3] at h2
  have h32 : f (3 / 2 : ℝ) ≠ 0 := by
    apply h'
  -- $f(3/2) = f(3) \cdot f(3/2)$ implies $f(3) = 1$
  have h2' : f 3 = 1 := by
    apply (mul_left_inj' h32).mp
    linarith
  exact h2'