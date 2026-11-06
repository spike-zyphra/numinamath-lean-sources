import Mathlib
/- Let $a, b, c$ be nonnegative real numbers such that $bc + ca + ab = \frac{1}{3}$. Prove that
\[
\frac{1}{a^2 - bc + 1} + \frac{1}{b^2 - ca + 1} + \frac{1}{c^2 - ab + 1} \leq 3.
\] -/
theorem inequalities_619358 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : b * c + c * a + a * b = 1 / 3) : 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) ≤ 3:= by
  -- First case: Handle when at least one of a, b, c is zero
  by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
  .
    -- Split into subcases based on which variable is zero
    rcases h0 with rfl | rfl | rfl
    all_goals
      ring_nf at h
      ring_nf
    .
      -- Subcase: a = 0
      rw [h]
      norm_num
      -- Reduce to proving a simpler inequality
      suffices (1 + b ^ 2)⁻¹ + (1 + c ^ 2)⁻¹ ≤ 3 / 2 by linarith
      field_simp
      -- Establish that the denominator is positive
      have g1 : (1 + b ^ 2) * (1 + c ^ 2) > 0:= by positivity
      -- Reformulate the inequality
      suffices (1 + c ^ 2 + (1 + b ^ 2)) ≤ (3 / 2) * ((1 + b ^ 2) * (1 + c ^ 2)) by exact (div_le_iff₀ g1).mpr this
      ring_nf
      -- Use the constraint to establish a lower bound
      have g2 : b ^ 2 + c ^ 2 ≥ 2 * (1 / 3):= by
        rw [←h]
        linarith [sq_nonneg (b - c)]
      rw [show c ^ 2 * b ^ 2 = (b * c) ^ 2 by ring, h]
      linarith
    .
      -- Subcase: b = 0
      rw [show c * a = a * c by ring] at h
      rw [h]
      norm_num
      -- Reduce to proving a simpler inequality
      suffices (1 + c ^ 2)⁻¹ + (1 + a ^ 2)⁻¹ ≤ 3 / 2 by linarith
      field_simp
      -- Establish that the denominator is positive
      have g1 : (1 + c ^ 2) * (1 + a ^ 2) > 0:= by positivity
      -- Reformulate the inequality
      suffices (1 + a ^ 2 + (1 + c ^ 2)) ≤ (3 / 2) * ((1 + c ^ 2) * (1 + a ^ 2)) by exact (div_le_iff₀ g1).mpr this
      ring_nf
      -- Use the constraint to establish a lower bound
      have g2 : c ^ 2 + a ^ 2 ≥ 2 * (1 / 3):= by
        rw [←h]
        linarith [sq_nonneg (c - a)]
      rw [show a ^ 2 * c ^ 2 = (a * c) ^ 2 by ring, h]
      linarith
    .
      -- Subcase: c = 0
      rw [show b * a = a * b by ring] at h
      rw [h]
      norm_num
      -- Reduce to proving a simpler inequality
      suffices (1 + a ^ 2)⁻¹ + (1 + b ^ 2)⁻¹ ≤ 3 / 2 by linarith
      field_simp
      -- Establish that the denominator is positive
      have g1 : (1 + a ^ 2) * (1 + b ^ 2) > 0:= by positivity
      -- Reformulate the inequality
      suffices (1 + b ^ 2 + (1 + a ^ 2)) ≤ (3 / 2) * ((1 + a ^ 2) * (1 + b ^ 2)) by exact (div_le_iff₀ g1).mpr this
      ring_nf
      -- Use the constraint to establish a lower bound
      have g2 : a ^ 2 + b ^ 2 ≥ 2 * (1 / 3):= by
        rw [←h]
        linarith [sq_nonneg (a - b)]
      rw [show b ^ 2 * a ^ 2 = (a * b) ^ 2 by ring, h]
      linarith
  .
    -- Second case: All of a, b, c are strictly positive
    simp at h0
    rcases h0 with ⟨ha1, hb1, hc1⟩
    -- Strengthen the nonnegativity to strict positivity
    replace ha : a > 0:= by positivity
    replace hb : b > 0:= by positivity
    replace hc : c > 0:= by positivity
    clear ha1 hb1 hc1
    -- Rewrite the constraint for easier manipulation
    replace h : 3 * (b * c + c * a + a * b) = 1:= by linarith
    -- Rewrite the denominators in the original inequality
    rw [show a ^ 2 - b * c + 1 = a * (a + b + c) + 2 * (a * b + b * c + c * a) by rw [←h] ; linarith]
    rw [show b ^ 2 - c * a + 1 = b * (a + b + c) + 2 * (a * b + b * c + c * a) by rw [←h] ; linarith]
    rw [show c ^ 2 - a * b + 1 = c * (a + b + c) + 2 * (a * b + b * c + c * a) by rw [←h] ; linarith]
    rw [←h]
    clear h
    -- Rewrite each fraction in a more manageable form
    rw [show 3 * (b * c + c * a + a * b) / (a * (a + b + c) + 2 * (a * b + b * c + c * a)) = 3 / 2 * (1 - (a + b + c) * (a / (a * (a + b + c) + 2 * (a * b + b * c + c * a)))) by field_simp ; linarith]
    rw [show 3 * (b * c + c * a + a * b) / (b * (a + b + c) + 2 * (a * b + b * c + c * a)) = 3 / 2 * (1 - (a + b + c) * (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a)))) by field_simp ; linarith]
    rw [show 3 * (b * c + c * a + a * b) / (c * (a + b + c) + 2 * (a * b + b * c + c * a)) = 3 / 2 * (1 - (a + b + c) * (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a)))) by field_simp ; linarith]
    -- Combine the terms and factor out 3/2
    rw [show  3 / 2 * (1 - (a + b + c) * (a / (a * (a + b + c) + 2 * (a * b + b * c + c * a)))) +
      3 / 2 * (1 - (a + b + c) * (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a)))) +
    3 / 2 * (1 - (a + b + c) * (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a)))) =  3 / 2 * ((1 - (a + b + c) * (a / (a * (a + b + c) + 2 * (a * b + b * c + c * a)))) +
      (1 - (a + b + c) * (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a)))) +
    (1 - (a + b + c) * (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a))))) by ring]
    -- Reduce to proving a lower bound
    suffices (a + b + c) * (a / (a * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (a + b + c) * (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (a + b + c) * (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a))) ≥ 1 by linarith
    -- Factor out (a+b+c)
    rw [show (a + b + c) * (a / (a * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (a + b + c) * (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (a + b + c) * (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a))) = (a + b + c) * ((a / (a * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (b / (b * (a + b + c) + 2 * (a * b + b * c + c * a))) +
    (c / (c * (a + b + c) + 2 * (a * b + b * c + c * a)))) by ring]
    -- Simplify the fractions
    rw [show a / (a * (a + b + c) + 2 * (a * b + b * c + c * a)) = a ^ 2 / (a ^ 2 * (a + b + c) + 2 * a * (a * b + b * c + c * a)) by field_simp ; linarith]
    rw [show b / (b * (a + b + c) + 2 * (a * b + b * c + c * a)) = b ^ 2 / (b ^ 2 * (a + b + c) + 2 * b * (a * b + b * c + c * a)) by field_simp ; linarith]
    rw [show c / (c * (a + b + c) + 2 * (a * b + b * c + c * a)) = c ^ 2 / (c ^ 2 * (a + b + c) + 2 * c * (a * b + b * c + c * a)) by field_simp ; linarith]
    -- Apply Cauchy-Schwarz inequality
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
      (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
      intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
      have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
      linarith
    -- Reformulate the Cauchy-Schwarz inequality for our specific case
    replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
      (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
      intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
      -- Apply square root properties
      have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
      have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
      have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
      have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
      have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
      have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
      -- Apply the Cauchy-Schwarz inequality with transformed variables
      have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      rw [g1, g2, g3, g4, g5, g6] at h1
      -- Simplify the expressions
      rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
      rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
      rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
      exact h1
    -- Apply the inequality with our specific values
    specialize h1 a b c (a ^ 2 * (a + b + c) + 2 * a * (a * b + b * c + c * a)) (b ^ 2 * (a + b + c) + 2 * b * (a * b + b * c + c * a)) (c ^ 2 * (a + b + c) + 2 * c * (a * b + b * c + c * a)) ha hb hc (by positivity) (by positivity) (by positivity)
    -- Simplify the sum of denominators
    rw [show a ^ 2 * (a + b + c) + 2 * a * (a * b + b * c + c * a) + (b ^ 2 * (a + b + c) + 2 * b * (a * b + b * c + c * a)) + (c ^ 2 * (a + b + c) + 2 * c * (a * b + b * c + c * a)) = (a + b + c) ^ 3 by linarith] at h1
    -- Rewrite (a+b+c)^2 with a coefficient of 1
    rw [show (a + b + c) ^ 2 = 1 * (a + b + c) ^ 2 by simp] at h1
    -- Rearrange the inequality
    rw [show (a ^ 2 / (a ^ 2 * (a + b + c) + 2 * a * (a * b + b * c + c * a)) +
        b ^ 2 / (b ^ 2 * (a + b + c) + 2 * b * (a * b + b * c + c * a)) +
      c ^ 2 / (c ^ 2 * (a + b + c) + 2 * c * (a * b + b * c + c * a))) *
    (a + b + c) ^ 3 = (a + b + c) * (a ^ 2 / (a ^ 2 * (a + b + c) + 2 * a * (a * b + b * c + c * a)) +
        b ^ 2 / (b ^ 2 * (a + b + c) + 2 * b * (a * b + b * c + c * a)) +
      c ^ 2 / (c ^ 2 * (a + b + c) + 2 * c * (a * b + b * c + c * a))) *
    (a + b + c) ^ 2 by ring] at h1
    -- Establish that (a+b+c)^2 is positive
    have g1 : (a + b + c) ^ 2 > 0:= by positivity
    -- Complete the proof by dividing both sides by (a+b+c)^2
    exact le_of_mul_le_mul_right h1 g1
