import Mathlib

/- Let $a,$ $b,$ and $c$ be positive real numbers.  Find the minimum value of
\[\frac{(a + b + c)[(a + b)^2 + (a + b + 4c)^2]}{abc}.\]-/
theorem algebra_20464 : IsLeast {z | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    z = (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c)} 100 := by
  -- By AM-GM,
  --\[a + b \ge 2 \sqrt{ab},\]so $(a + b)^2 \ge 4ab.$
  have amgm2 (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    suffices 0 ≤ (a + b) ^ 2 - 4 * a * b by linarith
    convert_to 0 ≤ (a - b) ^ 2
    . ring
    positivity
  have amgm5 {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
      5 * (a * b * c * d * e) ^ (1 / 5 : ℝ) ≤ a + b + c + d + e := by
    rw [← le_div_iff₀' (by norm_num)]
    let w : ℕ → ℝ := fun n => 1 / 5
    let z : ℕ → ℝ := fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => 0
    have : ∏ i ∈ Finset.range 5, z i ^ w i ≤ ∑ i ∈ Finset.range 5, w i * z i := by
      apply Real.geom_mean_le_arith_mean_weighted
      . intro i hi
        simp at hi
        interval_cases i
        all_goals norm_num
      . simp [w]
      intro i hi
      simp at hi
      interval_cases i
      all_goals simpa [z]
    convert this
    . repeat rw [Real.mul_rpow (by positivity) (by positivity)]
      simp [Finset.prod_range_succ, z, w]
    field_simp
    simp [Finset.sum_range_succ, w, z]
    ring
  have cast_rpow5 (x : ℝ) : x ^ (5 : ℝ) = x ^ 5 := by norm_cast
  constructor
  . -- Equality occurs when $a = b = 2$ and $c = 1,$ so the minimum value is $\boxed{100}.$
    -- Verify that given a=b=2 and c=1 we have $(a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) = 100$.
    use 2, 2, 1
    norm_num
  simp [lowerBounds]
  intro z a ha b hb c hc hz
  rw [hz, le_div_iff₀ (by positivity)]
  --   Also by AM-GM,
  -- \[(a + 2c) + (b + 2c) \ge 2 \sqrt{(a + 2c)(b + 2c)},\]so $(a + b + 4c)^2 \ge 4(a + 2c)(b + 2c).$
  --   Hence,
  -- \begin{align*}
  -- (a + b)^2 + (a + b + 4c)^2 &\ge 4ab + 4(a + 2c)(b + 2c) \\
  -- &= 8ab + 8ac + 8bc + 16c^2 \\
  -- &= 8(ab + ac + bc + 2c^2).
  -- \end{align*}
  have h1 : 8 * (a * b + a * c + b * c + 2 * c ^ 2) ≤ (a + b)^2 + (a + b + 4 * c)^2 := by
    have h1 := amgm2 a b
    have h2 := amgm2 (a + 2 * c) (b + 2 * c)
    have := add_le_add h1 h2
    convert this using 1
    all_goals ring
  --   By AM-GM,
  -- \begin{align*}
  -- ab + ac + bc + 2c^2 &= \frac{ab}{2} + \frac{ab}{2} + ac + bc + 2c^2 \\
  -- &\ge 5 \sqrt[5]{\frac{ab}{2} \cdot \frac{ab}{2} \cdot ac \cdot bc \cdot 2c^2} \\
  -- &= 5 \sqrt[5]{\frac{a^3 b^3 c^4}{2}}.
  -- \end{align*}
  have h2 : 5 * (a ^ 3 * b ^ 3 * c ^ 4 / 2) ^ (1 / 5 : ℝ) ≤ a * b + a * c + b * c + 2 * c ^ 2 := by
    have := @amgm5 (a * b / 2) (a * b / 2) (a * c) (b * c) (2 * c ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    convert this using 1
    . congr
      ring
    ring
  replace h2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (8 : ℝ) by norm_num)
  --   Also by AM-GM,
  -- \begin{align*}
  -- a + b + c &= \frac{a}{2} + \frac{a}{2} + \frac{b}{2} + \frac{b}{2} + c \\
  -- &\ge 5 \sqrt[5]{\frac{a}{2} \cdot \frac{a}{2} \cdot \frac{b}{2} \cdot \frac{b}{2} \cdot c} \\
  -- &= 5 \sqrt[5]{\frac{a^2 b^2 c}{16}}.
  -- \end{align*}
  have h3 : 5 * (a ^ 2 * b ^ 2 * c / 16) ^ (1 / 5 : ℝ) ≤ a + b + c := by
    have := @amgm5 (a / 2) (a / 2) (b / 2) (b / 2) c
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    convert this using 1
    . congr
      ring
    ring
  --   Hence,
  -- \begin{align*}
  -- \frac{(a + b + c)[(a + b)^2 + (a + b + 4c)^2]}{abc} &\ge 8 \cdot \frac{5 \sqrt[5]{\frac{a^2 b^2 c}{16}} \cdot 5 \sqrt[5]{\frac{a^3 b^3 c^4}{2}}}{abc} \\
  -- &= 100.
  -- \end{align*}
  have := h2.trans h1
  have := mul_le_mul h3 this (by positivity) (by positivity)
  convert this using 1
  rw [← Real.rpow_left_inj (z := 5)]
  conv_rhs =>
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr
    . rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by positivity),
        show 1 / 5 * 5 = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity),
      show 1 / 5 * 5 = (1 : ℝ) by norm_num, Real.rpow_one]
  field_simp
  repeat rw [cast_rpow5]
  ring
  all_goals positivity
