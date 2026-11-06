import Mathlib

/- Show that for any positive real numbers $a, b, c$ such that $a+b+c=a b+b c+c a$, the following inequality holds

$$
3+\sqrt[3]{\frac{a^{3}+1}{2}}+\sqrt[3]{\frac{b^{3}+1}{2}}+\sqrt[3]{\frac{c^{3}+1}{2}} \leqslant 2(a+b+c)
$$ -/
theorem inequalities_605998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = a * b + b * c + c * a) :
  3 + ((a ^ 3 + 1) / 2) ^ (1 / 3 : ℝ) + ((b ^ 3 + 1) / 2) ^ (1 / 3 : ℝ) + ((c ^ 3 + 1) / 2) ^ (1 / 3 : ℝ) ≤ 2 * (a + b + c) := by
  -- We prove that ((a ^ 3 + 1) / 2) ^ (1 / 3 : ℝ) ≤ (5 * a + 2 * b + 2 * c - 3) / 6.
  have H {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = a * b + b * c + c * a) : ((a ^ 3 + 1) / 2) ^ (1 / 3 : ℝ) ≤ (5 * a + 2 * b + 2 * c - 3) / 6 := by
    -- (a ^ 3 + 1) / 2 = ((a + 1) / 2) * (a ^ 2 - a + 1)
    -- = ((a + 1) / 2) * ((c + a - 1) * (a + b - 1))
    -- The three terms are all non-negative, so we can apply AM-GM.
    have hp₁ : 0 ≤ (a + 1) / 2 := by positivity
    have hp₂ : 0 ≤ c + a - 1 := by nlinarith
    have hp₃ : 0 ≤ a + b - 1 := by nlinarith
    calc ((a ^ 3 + 1) / 2) ^ (1 / 3 : ℝ)
      _ = ((a + 1) / 2 * (a ^ 2 - a + 1)) ^ (1 / 3 : ℝ) := by congr; ring
      _ = ((a + 1) / 2 * ((c + a - 1) * (a + b - 1))) ^ (1 / 3 : ℝ) := by congr; linear_combination h
      _ = ((a + 1) / 2 * (c + a - 1) * (a + b - 1)) ^ (1 / 3 : ℝ) := by rw [mul_assoc]
      _ = ((a + 1) / 2) ^ (1 / 3 : ℝ) * (c + a - 1) ^ (1 / 3 : ℝ) * (a + b - 1) ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow, Real.mul_rpow]
        all_goals positivity
      -- Apply AM-GM.
      _ ≤ 1 / 3 * ((a + 1) / 2) + 1 / 3 * (c + a - 1) + 1 / 3 * (a + b - 1) := Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num) hp₁ hp₂ hp₃ (by norm_num)
      -- Now simplify RHS and we get the result.
      _ = (5 * a + 2 * b + 2 * c - 3) / 6 := by ring
  -- Do the same for the other terms.
  have H₁ := H ha hb hc h
  have H₂ := H hb hc ha (by linear_combination h)
  have H₃ := H hc ha hb (by linear_combination h)
  -- Now we prove that 3 ≤ a + b + c.
  have h₁ : 3 ≤ a + b + c := by
    -- Multiply both sides by a + b + c
    suffices H : 3 * (a + b + c) ≤ (a + b + c) * (a + b + c) from le_of_mul_le_mul_right H (by positivity)
    -- Rewrite the LHS.
    nth_rw 1 [h]
    -- Now it is a well-known inequality.
    linarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Now we can prove the main result.
  linarith only [H₁, H₂, H₃, h₁]
