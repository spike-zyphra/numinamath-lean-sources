import Mathlib

/-Let $x$ and $y$ be real numbers such that $0 \le x \le 1$ and $0 \le y \le 1.$  Find the maximum value of
\[x^2 y - xy^2.\]-/
theorem algebra_20844 : IsGreatest {k : ℝ | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ k = x^2*y - x*y^2 } (1/4) := by
  constructor
  · -- when x = 1, y = 1 / 2, $x^2y - xy^2 = \frac 1 4$
    simp
    use 1
    simp
    use 1 / 2
    norm_num
  · intro a h
    simp at h
    obtain ⟨x, x1, x2, y, y1, y2, h⟩ := h
    -- We can factor the expression as
    -- \[xy (x - y).\]
    suffices x * y * (x - y) ≤ 1 / 4 by nlinarith
    have am_gm (a b : ℝ) : a * b ≤ (a + b)^2 / 4 := by
      norm_num [le_div_iff₀]
      have : 0 ≤ (a - b)^2 := by nlinarith
      nlinarith
    calc
      -- Since we are trying to find the maximum, we can assume that $x \ge y.$  Then by AM-GM, \[y(x - y) \le \frac{x^2}{4},\], so
      -- \[xy (x - y) \le x \cdot \frac{x^2}{4} = \frac{x^3}{4} \le \frac{1}{4}.\]
      _ ≤ x * (x^2 / 4) := by nlinarith [am_gm y (x - y)]
      _ = x^3 / 4 := by nlinarith
      _ ≤ 1 / 4 := by norm_num [le_div_iff₀]; nlinarith


