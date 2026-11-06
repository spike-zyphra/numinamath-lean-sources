import Mathlib

/- Let $a, b$, and $c$ be positive real numbers satisfying $a^{b}>b^{a}$ and $b^{c}>c^{b}$. Does it follow that $a^{c}>c^{a}$ ? -/
theorem inequalities_258473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^b > b^a) (h2 : b^c > c^b) : a^c > c^a := by
  -- First, we convert a^b > b^a to b*log(a) > a*log(b) using logarithm properties
  have h10 : b * Real.log a > a * Real.log b := by
    -- Apply logarithm to both sides of a^b > b^a
    have h11 : Real.log (a ^ b) > Real.log (b ^ a) := by
      -- Prove b^a > 0 to use log_lt_log
      have h13 : b ^ a > 0 := by positivity
      exact Real.log_lt_log (by positivity) (by linarith [h1, h13])
    -- Simplify log(a^b) to b*log(a)
    have h14 : Real.log (a ^ b) = b * Real.log a := by
      rw [Real.log_rpow]
      all_goals linarith
    -- Simplify log(b^a) to a*log(b)
    have h15 : Real.log (b ^ a) = a * Real.log b := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h14, h15, h11]
  -- Similarly, convert b^c > c^b to c*log(b) > b*log(c)
  have h16 : c * Real.log b > b * Real.log c := by
    -- Apply logarithm to both sides of b^c > c^b
    have h17 : Real.log (b ^ c) > Real.log (c ^ b) := by
      -- Prove c^b > 0 to use log_lt_log
      have h19 : c ^ b > 0 := by positivity
      exact Real.log_lt_log (by positivity) (by linarith [h2, h19])
    -- Simplify log(b^c) to c*log(b)
    have h20 : Real.log (b ^ c) = c * Real.log b := by
      rw [Real.log_rpow]
      all_goals linarith
    -- Simplify log(c^b) to b*log(c)
    have h21 : Real.log (c ^ b) = b * Real.log c := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h20, h21, h17]
  -- Use nonlinear arithmetic to prove c*log(a) > a*log(c) from the previous inequalities
  have h22 : c * Real.log a > a * Real.log c := by
    nlinarith [h10, h16, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  -- Convert c*log(a) > a*log(c) back to log(a^c) > log(c^a)
  have h24 : Real.log (a ^ c) > Real.log (c ^ a) := by
    -- Simplify log(a^c) to c*log(a)
    have h25 : Real.log (a ^ c) = c * Real.log a := by
      rw [Real.log_rpow]
      all_goals linarith
    -- Simplify log(c^a) to a*log(c)
    have h26 : Real.log (c ^ a) = a * Real.log c := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h22, h25, h26]
  -- Finally, convert log(a^c) > log(c^a) back to a^c > c^a
  have h27 : a ^ c > c ^ a := by
    -- Prove a^c > 0 and c^a > 0 to use log_lt_log_iff
    have h29 : a ^ c > 0 := by positivity
    have h30 : c ^ a > 0 := by positivity
    exact (Real.log_lt_log_iff (by linarith) (by linarith)).mp h24
  exact h27
