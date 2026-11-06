import Mathlib

open Real

/- 13 Let $a, b \in \mathbf{R}^{+}$, prove that $\sqrt{a}+1>\sqrt{b}$ holds if and only if for any $x>1$, $a x+\frac{x}{x-1}>b$. -/
theorem inequalities_597741 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    √a + 1 > √b ↔ ∀ x > 1, a * x + x / (x - 1) > b := by
  constructor
  · -- Proof of the forward direction: √a + 1 > √b → ∀ x > 1, a * x + x / (x - 1) > b
    intro h
    intro x hx
    -- We'll prove that a * x + x / (x - 1) - b > 0
    have h2 : a * x + x / (x - 1) - b > 0 := by
      -- First, we show that (√a + 1)² > b
      have h3 : (√a + 1) ^ 2 > b := by
        have h4 : √a + 1 > √b := h
        -- Square both sides of the inequality
        have h5 : (√a + 1) ^ 2 > (√b) ^ 2 := by nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h4]
        have h6 : (√b) ^ 2 = b := Real.sq_sqrt (by linarith)
        nlinarith
      -- Next, we prove that a * x + x / (x - 1) ≥ (√a + 1)²
      have h4 : a * x + x / (x - 1) ≥ (√a + 1) ^ 2 := by
        have h5 : (√a) ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
        -- The square of any real number is non-negative
        have h6 : (√a * (x - 1) - 1) ^ 2 ≥ 0 := by
          apply sq_nonneg
        -- Division by a positive number preserves non-negativity
        have h7 : (√a * (x - 1) - 1) ^ 2 / (x - 1) ≥ 0 := by
          apply div_nonneg
          · exact h6
          · linarith
        -- Key algebraic manipulation: expressing the difference as a non-negative term
        have h8 : a * x + x / (x - 1) - (√a + 1) ^ 2 = (√a * (x - 1) - 1) ^ 2 / (x - 1) := by
          have h9 : x - 1 ≠ 0 := by linarith
          field_simp [h9]
          ring_nf
          nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith)]
        linarith [h8, h7]
      -- Combine the inequalities to get our result
      nlinarith [h3, h4]
    linarith
  · -- Proof of the backward direction: ∀ x > 1, a * x + x / (x - 1) > b → √a + 1 > √b
    intro h
    -- We'll first prove that (√a + 1)² > b
    have h1 : (√a + 1) ^ 2 > b := by
      -- Since a > 0, we have √a > 0
      have h2 : √a > 0 := Real.sqrt_pos.2 (by linarith)
      -- Show that 1 + 1/√a > 1
      have h3 : 1 + 1 / √a > 1 := by
        have h4 : 1 / √a > 0 := by
          apply div_pos
          · norm_num
          · linarith
        linarith
      -- Apply our hypothesis with x = 1 + 1/√a
      have h4 := h (1 + 1 / √a) h3
      -- Prove that for this specific value of x, a * x + x / (x - 1) = (√a + 1)²
      have h5 : a * (1 + 1 / √a) + (1 + 1 / √a) / ((1 + 1 / √a) - 1) = (√a + 1) ^ 2 := by
        -- Express 1 + 1/√a in a different form
        have h6 : (1 : ℝ) + 1 / √a = (√a + 1) / √a := by
          field_simp [h2.ne.symm]
        -- Simplify the second term
        have h7 : (1 + 1 / √a) / ((1 + 1 / √a) - 1) = √a + 1 := by
          rw [h6]
          have h8 : (√a + 1) / √a / ((√a + 1) / √a - 1) = √a + 1 := by
            have h9 : (√a + 1) / √a - 1 = 1 / √a := by
              field_simp [h2.ne.symm]
            rw [h9]
            field_simp [h2.ne.symm]
          rw [h8]
        -- Simplify the first term
        have h10 : a * (1 + 1 / √a) = √a * √a + √a := by
          have h11 : √a * √a = a := by
            exact Real.mul_self_sqrt (by linarith)
          field_simp [h2.ne.symm]
          nlinarith [h11]
        linarith [h7, h10]
      -- Combine the results to get (√a + 1)² > b
      nlinarith [h5, h4]
    -- Finally, prove that √a + 1 > √b
    have h2 : √a + 1 > √b := by
      -- If (√a + 1)² > (√b)², then √a + 1 > √b (since both sides are positive)
      have h3 : (√a + 1) ^ 2 > (√b) ^ 2 := by
        have h4 : (√b) ^ 2 = b := Real.sq_sqrt (by linarith)
        nlinarith [h1, h4]
      -- Verify that both sides are non-negative
      have h4 : 0 ≤ √a + 1 := by
        linarith [Real.sqrt_nonneg a]
      have h5 : 0 ≤ √b := Real.sqrt_nonneg b
      -- Apply the property that for non-negative x and y, if x² > y² then x > y
      nlinarith [sq_nonneg (√a + 1 - √b), h3, h4, h5]
    linarith
