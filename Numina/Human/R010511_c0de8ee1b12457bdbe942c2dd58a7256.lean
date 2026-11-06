import Mathlib

/- Let's prove that if $a, b, c$ are real numbers, then


$$

\sqrt{a^{2}+b^{2}-a b}+\sqrt{b^{2}+c^{2}-b c} \geq \sqrt{a^{2}+c^{2}+a c}

$$
 -/
theorem inequalities_200603 (a b c : ℝ) :
    √ (a^2 + b^2 - a * b) + √ (b^2 + c^2 - b * c) ≥
    √ (a^2 + c^2 + a * c) := by
  -- first prove that p^2 + q^2 + pq and p^2 + q^2 - pq are nonnegative, so square roots make sense and facts about them can be used
  have aux₁ (a b: ℝ) : 0 ≤ a^2 + b^2 - a*b := by
    obtain h | h := le_or_lt 0 (a*b)
    . linarith [(show 0 ≤ (a-b)^2 by positivity)]
    . linarith [(show 0 ≤ (a+b)^2 by positivity)]
  have aux₂ (a b: ℝ) : 0 ≤ a^2 + b^2 + a*b := by
    obtain h | h := le_or_lt 0 (a*b)
    . linarith [(show 0 ≤ (a-b)^2 by positivity)]
    . linarith [(show 0 ≤ (a+b)^2 by positivity)]
  have hab := aux₁ a b
  have hbc := aux₁ b c
  have hac := aux₂ a c
  -- now we'll prove squared version of inequalities, square and simplify
  apply sq_le_sq₀ (by positivity) (by positivity) |>.mp
  simp [hac]
  ring_nf at *
  simp [hab, hbc]; rw [← Real.sqrt_mul hab]
  -- the inequality is equivalent to following
  suffices a*b + a*c + b*c - 2*b^2 ≤ 2 * √((-(a * b) + a ^ 2 + b ^ 2) * (-(c * b) + c ^ 2 + b ^ 2)) by linarith only [this]
  -- if left side is negative, we're done as rhs is nonnegative, otherwise again prove squared version which is equivalent to 3 * (a*b + b*c - a*c)^2 ≥ 0
  obtain h | h := le_or_lt 0 (a*b + a*c + b*c - 2*b^2)
  . apply sq_le_sq₀ (by positivity) (by positivity) |>.mp
    rw [mul_pow 2]
    rw [Real.sq_sqrt (by positivity)]
    linarith [show (a*b + b*c - a*c)^2 ≥ 0 by positivity]
  . have : 0 ≤ 2 * √((-(a * b) + a ^ 2 + b ^ 2) * (-(c * b) + c ^ 2 + b ^ 2)) := by positivity
    linarith