import Mathlib
open Real
set_option maxHeartbeats 800000
/- 10.3. Prove the inequality $\sqrt{x^{3}+y}+\sqrt{y^{3}+x} \geq \sqrt{x^{3}+x}+\sqrt{y^{3}+y}$. -/
theorem inequalities_235610 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) :
    √(x^3 + y) + √(y^3 + x) ≥ √(x^3 + x) + √(y^3 + y) := by
  -- Main proof statement
  have h1 : √(x^3 + y) + √(y^3 + x) ≥ √(x^3 + x) + √(y^3 + y) := by
    -- We'll square both sides of the inequality to simplify
    have h1 : (√(x^3 + y) + √(y^3 + x)) ^ 2 ≥ (√(x^3 + x) + √(y^3 + y)) ^ 2 := by
      -- Expand the square of the left side using (a+b)² = a² + b² + 2ab
      have h3 : (√(x^3 + y) + √(y^3 + x)) ^ 2 = (√(x^3 + y)) ^ 2 + (√(y^3 + x)) ^ 2 + 2 * (√(x^3 + y) * √(y^3 + x)) := by
        ring
      -- Expand the square of the right side using (a+b)² = a² + b² + 2ab
      have h4 : (√(x^3 + x) + √(y^3 + y)) ^ 2 = (√(x^3 + x)) ^ 2 + (√(y^3 + y)) ^ 2 + 2 * (√(x^3 + x) * √(y^3 + y)) := by
        ring
      rw [h3, h4]
      -- Simplify (√(x³+y))² = x³+y
      have h5 : (√(x^3 + y)) ^ 2 = x^3 + y := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg x, sq_nonneg y, hx, hy]
      -- Simplify (√(y³+x))² = y³+x
      have h6 : (√(y^3 + x)) ^ 2 = y^3 + x := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg x, sq_nonneg y, hx, hy]
      -- Simplify (√(x³+x))² = x³+x
      have h7 : (√(x^3 + x)) ^ 2 = x^3 + x := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg x, hx]
      -- Simplify (√(y³+y))² = y³+y
      have h8 : (√(y^3 + y)) ^ 2 = y^3 + y := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg y, hy]
      rw [h5, h6, h7, h8]
      -- Prove that √(x³+y)·√(y³+x) ≥ √(x³+x)·√(y³+y)
      have h9 : √(x^3 + y) * √(y^3 + x) ≥ √(x^3 + x) * √(y^3 + y) := by
        -- Square both sides of the inequality
        have h10 : (√(x^3 + y) * √(y^3 + x)) ^ 2 ≥ (√(x^3 + x) * √(y^3 + y)) ^ 2 := by
          -- Simplify (√a·√b)² = a·b
          have h11 : (√(x^3 + y) * √(y^3 + x)) ^ 2 = (√(x^3 + y)) ^ 2 * (√(y^3 + x)) ^ 2 := by ring
          have h12 : (√(x^3 + x) * √(y^3 + y)) ^ 2 = (√(x^3 + x)) ^ 2 * (√(y^3 + y)) ^ 2 := by ring
          rw [h11, h12]
          rw [h5, h6, h7, h8]
          -- Use nonlinear arithmetic to prove the inequality
          nlinarith [sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y), sq_nonneg (x^2 + x * y + y^2)]
        -- Prove that √(x³+y)·√(y³+x) ≥ 0
        have h13 : √(x^3 + y) * √(y^3 + x) ≥ 0 := by
          apply mul_nonneg
          · apply Real.sqrt_nonneg
          · apply Real.sqrt_nonneg
        -- Prove that √(x³+x)·√(y³+y) ≥ 0
        have h14 : √(x^3 + x) * √(y^3 + y) ≥ 0 := by
          apply mul_nonneg
          · apply Real.sqrt_nonneg
          · apply Real.sqrt_nonneg
        -- Use nonlinear arithmetic to complete the proof
        nlinarith [h13, h14, sq_nonneg (√(x^3 + y) * √(y^3 + x) - √(x^3 + x) * √(y^3 + y)), h10]
      -- Use nonlinear arithmetic to complete the proof of the squared inequality
      nlinarith [h9]
    -- Prove that √(x³+y) + √(y³+x) ≥ 0
    have h2 : √(x^3 + y) + √(y^3 + x) ≥ 0 := by
      apply add_nonneg
      · apply Real.sqrt_nonneg
      · apply Real.sqrt_nonneg
    -- Prove that √(x³+x) + √(y³+y) ≥ 0
    have h3 : √(x^3 + x) + √(y^3 + y) ≥ 0 := by
      apply add_nonneg
      · apply Real.sqrt_nonneg
      · apply Real.sqrt_nonneg
    -- Use nonlinear arithmetic to derive the original inequality from the squared inequality
    nlinarith [sq_nonneg (√(x^3 + y) + √(y^3 + x) - (√(x^3 + x) + √(y^3 + y))), h1, h2, h3]
  -- Complete the proof by using the derived result
  exact h1
