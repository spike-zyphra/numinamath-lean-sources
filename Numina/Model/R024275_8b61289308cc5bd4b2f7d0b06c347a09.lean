import Mathlib

theorem inequalities_602424
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 ≤ 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 := by

  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 ≥ 1 / (1 + x * y) := by
    intro x y hx hy
    have h1 : 0 < (1 + x) * (1 + y) := by positivity
    have h2 : 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y) ≥ 0 := by
      have h3 : 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y) = 
        ((1 + y) ^ 2 * (1 + x * y) + (1 + x) ^ 2 * (1 + x * y) - (1 + x) ^ 2 * (1 + y) ^ 2) / ((1 + x) ^ 2 * (1 + y) ^ 2 * (1 + x * y)) := by
        field_simp
        ring
      rw [h3]
      apply div_nonneg
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1),
        mul_pos hx hy, mul_pos (show 0 < x * y by positivity) (show 0 < 1 by norm_num)]
      positivity
    linarith
  have h2 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 ≥ 1 / (1 + a * b) := by
    apply h1 a b ha hb
  have h3 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + c * d) := by
    apply h1 c d hc hd
  -- Now we need to show that $\frac{1}{1 + a \cdot b} + \frac{1}{1 + c \cdot d} \ge 1$.
  have h4 : a * b > 0 := mul_pos ha hb
  have h5 : c * d > 0 := mul_pos hc hd
  have h6 : c * d = 1 / (a * b) := by
    -- From `h : a * b * c * d = 1`, we solve for `c * d`.
    field_simp
    nlinarith
  have h7 : 1 / (1 + a * b) + 1 / (1 + c * d) ≥ 1 := by
    rw [show c * d = 1 / (a * b) by linarith [h6]]
    -- Now we need to prove that `1 / (1 + a * b) + 1 / (1 + 1 / (a * b)) ≥ 1`
    -- But `1 / (1 + a * b) + 1 / (1 + 1 / (a * b)) = 1`, exactly.
    have h8 : 1 / (1 + a * b) + 1 / (1 + (1 / (a * b))) = 1 := by
      field_simp
      all_goals nlinarith
    nlinarith [h8]
  linarith [h2, h3, h7]