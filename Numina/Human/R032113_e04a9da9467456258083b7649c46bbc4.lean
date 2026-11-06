import Mathlib

/- If $x, y, k$ are positive reals such that

$$
3=k^{2}\left(\frac{x^{2}}{y^{2}}+\frac{y^{2}}{x^{2}}\right)+k\left(\frac{x}{y}+\frac{y}{x}\right),
$$

find the maximum possible value of $k$. -/
theorem number_theory_611197 :
    IsGreatest {k : ℝ | 0 < k ∧ ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 3 = k ^ 2 * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) + k * (x / y + y / x)} ((√7 - 1) / 2) := by
  constructor
  -- We first show that k = (√7 - 1) / 2 is possible
  . simp
    constructor
    -- k > 0
    . exact Real.lt_sqrt_of_sq_lt (by simp)
    -- x = y = 1
    . use 1, by simp, 1, by simp
      ring_nf
      simp
      norm_num
  -- We now show that any other k is less than (√7 - 1) / 2
  . intro k ⟨hk, x, y, hx, hy, h⟩
    -- It suffices to show that (2 * k + 1) ^ 2 ≤ 7
    suffices H : 2 * k + 1 ≤ √7 by linarith
    apply Real.le_sqrt_of_sq_le
    -- We show that a / b + b / a ≥ 2
    have lem {a b : ℝ} (ha : a > 0) (hb : b > 0) : a / b + b / a ≥ 2 := by
      -- Cancel the denominators, and use the fact that (a - b) ^ 2 ≥ 0
      field_simp
      rw [le_div_iff₀ (by positivity)]
      linarith only [sq_nonneg (a - b)]
    -- So 3 ≥ k ^ 2 * 2 + k * 2
    replace h : 3 ≥ k ^ 2 * 2 + k * 2 := by
      have hx' : x ^ 2 > 0 := by positivity
      have hy' : y ^ 2 > 0 := by positivity
      nlinarith [lem hx hy, lem hx' hy']
    -- So (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 ≤ 7
    linarith
