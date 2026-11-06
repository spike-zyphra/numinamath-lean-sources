import Mathlib

/- Find the maximum value of
\[\frac{x + 2y + 3}{\sqrt{x^2 + y^2 + 1}}\]over all real numbers $x$ and $y.$ -/
theorem algebra_15698 : IsGreatest {z : ℝ | ∃ x y, z = (x + 2*y + 3) / √(x^2 + y^2 + 1)} √14 := by
  -- Two goals:
  -- 1. Show that √14 can be achieved
  -- 2. Show that x + 2y + 3 / √(x^2 + y^2 + 1) ≤ √14
  constructor
  . -- Set x = 1/3, y = 2/3
    use 1/3, 2/3
    -- Simplify the expression
    field_simp
    ring_nf
    simp

  . -- We need to show that x + 2y + 3 / √(x^2 + y^2 + 1) ≤ √14
    rintro z ⟨x, y, rfl⟩
    -- Square both sides
    suffices h : ((x + 2 * y + 3) / √(x ^ 2 + y ^ 2 + 1))^2 ≤ 14 by
      rw [show 14 = √14^2 by simp] at h
      exact (abs_le_of_sq_le_sq' h (by simp)).2
    field_simp
    -- Cancel the denominator
    rw [div_le_iff₀ (by positivity)]
    -- Move the terms to the left hand side
    rw [← sub_nonneg, ← ge_iff_le]

    -- Complete the square
    calc _ = (3*x - 1)^2 + (3*y - 2)^2 + (2*x - y)^2 := by ring
         _ ≥ 0 := by positivity
