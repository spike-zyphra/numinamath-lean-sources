import Mathlib

/- Let $a, b, c$ be positive real numbers such that abc $=1$. Show that

$$
\frac{1}{a^{3}+b c}+\frac{1}{b^{3}+c a}+\frac{1}{c^{3}+a b} \leq \frac{(a b+b c+c a)^{2}}{6}
$$

so -/
theorem inequalities_604442 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :
    (1 / (a^3 + b * c)) + (1 / (b^3 + c * a)) + (1 / (c^3 + a * b)) ≤ (a * b + b * c + c * a)^2 / 6 := by
  -- We first show that 1 / (a^3 + b * c) ≤ b * c / 2.
  -- We generalize it to a, b, c > 0 and abc = 1 so that we can use it on b, c, a and c, a, b.
  have lem {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :
    1 / (a^3 + b * c) ≤ b * c / 2 := by
    -- Cancel the denominator.
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- Multiply both sides by a^2.
    refine le_of_mul_le_mul_of_pos_left ?_ (show a ^ 2 > 0 by positivity)
    calc
      -- LHS = 2 * a^2 ≤ a^4 + 1, by completing the square.
      _ ≤ a ^ 4 + 1 := by linarith only [sq_nonneg (a ^ 2 - 1)]
      -- = RHS, because a * b * c = 1.
      _ = a ^ 2 * (b * c * (a ^ 3 + b * c)) := by linear_combination ((-a ^ 4) - a * b * c - 1) * h
  -- Apply the lemma to a, b, c
  have h₁ := lem ha hb hc h
  -- Apply the lemma to b, c, a
  have h₂ := lem hb hc ha (by linear_combination h)
  -- Apply the lemma to c, a, b
  have h₃ := lem hc ha hb (by linear_combination h)
  -- We show that a * b + b * c + c * a ≥ 3.
  have H : a * b + b * c + c * a ≥ 3 := by
    -- Use the AM-GM inequality on a * b, b * c, c * a.
    have H := Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity) (by norm_num)
    -- Simplify the inequality.
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)] at H
    simp [show a * b * (b * c) * (c * a) = 1 by linear_combination (a * b * c + 1) * h] at H
    -- We get the desired inequality.
    linarith only [H]

  -- We now prove the main inequality.
  calc
    -- Use the lemma h₁, h₂, h₃
    _ ≤ b * c / 2 + c * a / 2 + a * b / 2 := by linarith only [h₁, h₂, h₃]
    -- Use the fact that a * b + b * c + c * a ≥ 3.
    _ ≤ (b * c / 2 + c * a / 2 + a * b / 2) * ((a * b + b * c + c * a) / 3) := le_mul_of_one_le_right (by positivity) (by linarith only [H])
    _ = (a * b + b * c + c * a) ^ 2 / 6 := by ring
