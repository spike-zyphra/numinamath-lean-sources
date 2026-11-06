import Mathlib
open Real

/-Alex picks his favorite point $(x, y)$ in the first quadrant on the unit circle $x^{2}+y^{2}=1$, such that a ray from the origin through $(x, y)$ is $\theta$ radians counterclockwise from the positive $x$-axis. He then computes $\cos ^{-1}\left(\frac{4 x+3 y}{5}\right)$ and is surprised to get $\theta$. What is $\tan (\theta)$ ?-/
theorem algebra_20001 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x^2 + y^2 = 1)
  (h : arccos ((4 * x + 3 * y) / 5) = arctan (y / x)) : tan (arctan (y / x)) = 1 / 3 := by
  -- Establish that $tan(arctan(y/x)) = y/x$, as $arctan(y/x)$ is the $angle θ.$
  have h₁ : tan (arctan (y / x)) = y / x := by
    rw [tan_arctan]
  -- Prove that $y/x = 1/3$ by using the given condition $arccos((4x + 3y)/5) = arctan(y/x)$.
  have h₂ : y / x = 1 / 3 := by
    have h₃ : arccos ((4 * x + 3 * y) / 5) = arctan (y / x) := h
    have h₄ : (4 * x + 3 * y) / 5 = Real.cos (arctan (y / x)) := by
      -- Prove $cos(arccos((4x + 3y)/5)) = (4x + 3y)/5$, ensuring $(4x + 3y)/5 ∈ [-1, 1]$.
      have h₄₁ : Real.cos (arccos ((4 * x + 3 * y) / 5)) = (4 * x + 3 * y) / 5 := by
        rw [Real.cos_arccos]<;>
        nlinarith [hx, hy, hxy, sq_nonneg (x - 4 / 5), sq_nonneg (y - 3 / 5)]
      rw [h₃] at h₄₁
      have h₆ : Real.cos (arctan (y / x)) = (4 * x + 3 * y) / 5 := by
        linarith
      linarith
    -- Compute $cos(arctan(y/x)) = x / sqrt(x² + y²)$ using the identity for $cos(arctan)$.
    have h₅ : Real.cos (arctan (y / x)) = x / Real.sqrt (x ^ 2 + y ^ 2) := by
      have h₆ : Real.cos (arctan (y / x)) = x / Real.sqrt (x ^ 2 + y ^ 2) := by
        rw [Real.cos_arctan]
        field_simp [Real.sqrt_eq_iff_eq_sq, add_comm, add_assoc, add_left_comm, mul_comm, mul_assoc, mul_left_comm]
      rw [h₆]
    -- Simplify $x / sqrt(x² + y²) = x$ since $sqrt(x² + y²) = 1$ from $x² + y² = 1$.
    have h₆ : x / Real.sqrt (x ^ 2 + y ^ 2) = x := by
      have h₇ : Real.sqrt (x ^ 2 + y ^ 2) = 1 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [hx, hy, hxy, sq_nonneg (x - 4 / 5), sq_nonneg (y - 3 / 5)]
      rw [h₇]
      field_simp [hx.ne', hy.ne']
    have h₇ : (4 * x + 3 * y) / 5 = x := by
      linarith
    -- Solve for $y/x = 1/3$ using the equation $(4x + 3y)/5 = x$.
    have h₈ : y / x = 1 / 3 := by
      have h₉ : 0 < x := hx
      have h₁₀ : 0 < y := hy
      have h₁₁ : 0 < x * y := mul_pos h₉ h₁₀
      field_simp [h₉.ne', h₁₀.ne'] at h₇ ⊢
      nlinarith [hx, hy, hxy, sq_nonneg (x - 4 / 5), sq_nonneg (y - 3 / 5)]
    exact h₈
  -- Combine $tan(arctan(y/x)) = y/x$ and $y/x = 1/3$ to conclude.
  rw [h₁, h₂]