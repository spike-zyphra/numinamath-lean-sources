import Mathlib

/-For $0 \le a, b, c \le 1$, prove that the cyclic sum $\sum \frac{a}{b+c} \ge 6\sqrt[3]{abc(1-a)(1-b)(1-c)}$.-/
theorem inequalities_614505 (a b c : ℝ)
  (ha : 0 ≤ a ∧ a ≤ 1)
  (hb : 0 ≤ b ∧ b ≤ 1)
  (hc : 0 ≤ c ∧ c ≤ 1)
  (hbc : b + c ≠ 0)
  (hac : c + a ≠ 0)
  (hab : a + b ≠ 0):
  a / (b + c) + b / (c + a) + c / (a + b) ≥ 6 * (a * b * c * (1 - a) * (1 - b) * (1 - c)) ^ ((1 : ℝ) / 3) := by

  -- first we show that 1 - x ≥ 0 for x = a, b, c
  have : a ≥ 0 := ha.1
  have : (1 - a) ≥ 0 := by linarith only [ha.2]

  have : b ≥ 0 := hb.1
  have : (1 - b) ≥ 0 := by linarith only [hb.2]

  have : c ≥ 0 := hc.1
  have : (1 - c) ≥ 0 := by linarith only [hc.2]

  -- 1. By the Arithmetic Mean-Geometric Mean Inequality (AM-GM), we have:
  -- [ \sqrt[3]{abc(1-a)(1-b)(1-c)} \le \frac{a(1-a) + b(1-b) + c(1-c)}{3} ]
  have h1 : (a * b * c * (1 - a) * (1 - b) * (1 - c)) ^ ((1 : ℝ) / 3) =
    (a * (1 - a)) ^ ((1 : ℝ) / 3) * (b * (1 - b)) ^ ((1 : ℝ) / 3) * (c * (1 - c)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow, ← Real.mul_rpow]
      congr 1
      ring
      all_goals positivity

  have h2 : (a * (1 - a)) ^ ((1 : ℝ) / 3) * (b * (1 - b)) ^ ((1 : ℝ) / 3) * (c * (1 - c)) ^ ((1 : ℝ) / 3) ≤
    (1 / 3) * (a * (1 - a)) + (1 / 3) * (b * (1 - b)) + (1 / 3) * (c * (1 - c)) := by
      apply Real.geom_mean_le_arith_mean3_weighted
      iterate 3 norm_num
      iterate 3 positivity
      norm_num

  -- 2. Multiplying both sides by 6, we get:
  -- [ 6\sqrt[3]{abc(1-a)(1-b)(1-c)} \le 2[a(1-a) + b(1-b) + c(1-c)] ]
  have h3 : 6 * (a * b * c * (1 - a) * (1 - b) * (1 - c)) ^ ((1 : ℝ) / 3) ≤
    2 * ((a * (1 - a)) + (b * (1 - b)) + (c * (1 - c))) := by
      rw [h1]
      linarith

  -- 3. For each term $a(1-a)$, $b(1-b)$, and $c(1-c)$, we apply the AM-GM inequality again: [ a(1-a) \le \left(\frac{a + (1-a)}{2}\right)^2 = \frac{1}{4} ]
  have h4 : a * (1 - a) ≤ 1 / 4 := by
    suffices h : 4 * a ^ 2 - 4 * a + 1 ≥ 0 by linarith
    rw [show 4 * a ^ 2 - 4 * a + 1 = (2 * a - 1) ^ 2 by ring]
    positivity

  -- 4. Similarly, we have: [ b(1-b) \le \frac{1}{4} \quad \text{and} \quad c(1-c) \le \frac{1}{4} ]
  have h5 : b * (1 - b) ≤ 1 / 4 := by
    suffices h : 4 * b ^ 2 - 4 * b + 1 ≥ 0 by linarith
    rw [show 4 * b ^ 2 - 4 * b + 1 = (2 * b - 1) ^ 2 by ring]
    positivity

  have h6 : c * (1 - c) ≤ 1 / 4 := by
    suffices h : 4 * c ^ 2 - 4 * c + 1 ≥ 0 by linarith
    rw [show 4 * c ^ 2 - 4 * c + 1 = (2 * c - 1) ^ 2 by ring]
    positivity

  -- 5. Adding these inequalities, we get: [ a(1-a) + b(1-b) + c(1-c) \le \frac{1}{4} + \frac{1}{4} + \frac{1}{4} = \frac{3}{4} ]
  have h7 : (a * (1 - a)) + (b * (1 - b)) + (c * (1 - c)) ≤ 3 / 4 := by
    rw [show (3 : ℝ) / 4 = 1 / 4 + 1 / 4 + 1 / 4 by norm_num]
    gcongr

  -- 6. Substituting this result back into the inequality from step 2, we obtain: [ 6\sqrt[3]{abc(1-a)(1-b)(1-c)} \le 2 \left(\frac{3}{4}\right) = \frac{3}{2} ]
  have h8 : 6 * (a * b * c * (1 - a) * (1 - b) * (1 - c)) ^ ((1 : ℝ) / 3) ≤ 3 / 2 := by
    linarith only [h1, h2, h7]

  -- 7. By Nesbitt's inequality, for $0 \le a, b, c \le 1$, we have: [ \sum \frac{a}{b+c} \ge \frac{3}{2} ]
  have h9 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    have hac' : a + c ≠ 0 := by rwa [add_comm]
    have hacbc : (a + c) * (b + c) ≠ 0 := by positivity
    have habbc : (a + b) * (b + c) ≠ 0 := by positivity
    have hacac : (a + b) * (a + c) ≠ 0 := by positivity

    have h8 : a / (b + c) + b / (c + a) + c / (a + b) = 3 / 2 + 1 / 2 * ((a - b)^2 / ((a + c) * (b + c)) + (a - c)^2 / ((a + b) * (b + c)) + (b - c)^2 / ((a + b) * (a + c))) := by
      field_simp
      ring
    rw [h8]

    simp
    apply add_nonneg
    apply add_nonneg
    all_goals positivity

  -- 8. Combining the results from steps 6 and 7, we conclude: [ \sum \frac{a}{b+c} \ge \frac{3}{2} \ge 6\sqrt[3]{abc(1-a)(1-b)(1-c)} ] [ \boxed{\sum \frac{a}{b+c} \ge 6\sqrt[3]{abc(1-a)(1-b)(1-c)}} ]
  linarith only [h8, h9]
