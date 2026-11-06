import Mathlib

open Real Set
open scoped BigOperators

/- Example 22 (Mathematical Problem 1434 from "Mathematical Bulletin") Let positive numbers $x, y, z$ be not equal to 1, and $xy + yz + zx = 1$. Try to find the maximum value of $f(x, y, z) = x(1-y^2)(1-z^2) + y(1-z^2)(1-x^2) + z(1-x^2)(1-y^2)$. -/
theorem algebra_274875 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b + b * c + c * a = 1 ∧ x = a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2)} (4 / 9 * sqrt 3) := by
  constructor
  -- First part: Show that 4/9*√3 is in the set (i.e., it's achievable)
  · -- Let's first show 4/9*√3 is achieved
    -- We'll use the symmetric case where a = b = c = sqrt(1/3)
    use sqrt (1 / 3), sqrt (1 / 3), sqrt (1 / 3)
    -- Prove that sqrt(1/3) > 0
    have h1 : sqrt (1 / 3) > 0 := by
      apply sqrt_pos.mpr
      norm_num
    -- Prove that sqrt(1/3) ≠ 1
    have h2 : sqrt (1 / 3) ≠ 1 := by
      intro h
      have h3 : (sqrt (1 / 3)) ^ 2 = 1 := by
        rw [h]
        ring
      have h4 : (sqrt (1 / 3)) ^ 2 = 1 / 3 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      rw [h4] at h3
      norm_num at h3
    -- Now we need to verify all conditions in the set definition
    constructor
    -- Prove a > 0
    · exact h1
    constructor
    -- Prove b > 0
    · exact h1
    constructor
    -- Prove c > 0
    · exact h1
    constructor
    -- Prove a ≠ 1
    · exact h2
    constructor
    -- Prove b ≠ 1
    · exact h2
    constructor
    -- Prove c ≠ 1
    · exact h2
    constructor
    -- Show that a * b + b * c + c * a = 1
    · -- Show that a * b + b * c + c * a = 1
      -- Calculate sqrt(1/3) * sqrt(1/3) = 1/3
      have h3 : sqrt (1 / 3) * sqrt (1 / 3) = 1 / 3 := by
        calc
          sqrt (1 / 3) * sqrt (1 / 3) = (sqrt (1 / 3)) ^ 2 := by ring
          _ = 1 / 3 := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      -- Use the value to verify the constraint
      linarith [h3]
    -- Show that f(x, y, z) = 4/9*√3 when x = y = z = sqrt(1/3)
    · -- Show that f(x, y, z) = 4/9*√3 when x = y = z = sqrt(1/3)
      have h4 : sqrt (1 / 3) * (1 - (sqrt (1 / 3)) ^ 2) * (1 - (sqrt (1 / 3)) ^ 2) + sqrt (1 / 3) * (1 - (sqrt (1 / 3)) ^ 2) * (1 - (sqrt (1 / 3)) ^ 2) + sqrt (1 / 3) * (1 - (sqrt (1 / 3)) ^ 2) * (1 - (sqrt (1 / 3)) ^ 2) = 4 / 9 * sqrt 3 := by
        -- Calculate (sqrt(1/3))² = 1/3
        have h5 : (sqrt (1 / 3)) ^ 2 = 1 / 3 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        -- Calculate 1 - (sqrt(1/3))² = 2/3
        have h6 : (1 - (sqrt (1 / 3)) ^ 2) = 2 / 3 := by
          rw [h5]
          norm_num
        rw [h6]
        -- Rewrite sqrt(1/3) as sqrt(3)/3
        have h7 : sqrt (1 / 3) = sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h7]
        ring_nf
      linarith [h4]
  -- Second part: Show that 4/9*√3 is the greatest value in the set
  · -- Now prove 4/9*√3 is the greatest value
    intro w
    rintro ⟨a, b, c, ha, hb, hc, _, _, _, h, hw⟩
    -- Simplify the expression for f(a,b,c)
    have h4 : a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) = 4 * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (b * c - b * a), sq_nonneg (c * a - c * b),
        h, sq_nonneg (a * b + b * c + c * a - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    rw [h4] at hw
    -- Prove that a*b*c ≤ sqrt(3)/9
    have h5 : a * b * c ≤ (sqrt 3) / 9 := by
      have h6 : (a * b + b * c + c * a) = 1 := h
      -- Prove that (a*b*c)² ≤ 1/27
      have h7 : (a * b * c) ^ 2 ≤ 1 / 27 := by
        have h8 : (a * b + b * c + c * a) ^ 3 = 1 := by
          rw [h6]
          norm_num
        -- Use AM-GM inequality: (a*b + b*c + c*a)³ ≥ 27*(a*b*c)²
        have h9 : (a * b + b * c + c * a) ^ 3 ≥ 27 * (a * b * c) ^ 2 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        nlinarith [h8, h9]
      -- Derive a*b*c ≤ sqrt(3)/9 from (a*b*c)² ≤ 1/27
      have h10 : a * b * c ≤ (sqrt 3) / 9 := by
        have h11 : (a * b * c) ^ 2 ≤ 1 / 27 := h7
        have h12 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3
        have h13 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith)
        nlinarith [sq_nonneg (a * b * c - sqrt 3 / 9), h11, Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num), h13]
      exact h10
    -- Conclude that f(a,b,c) = 4*(a*b*c) ≤ 4*sqrt(3)/9 = 4/9*sqrt(3)
    nlinarith [h5, Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
