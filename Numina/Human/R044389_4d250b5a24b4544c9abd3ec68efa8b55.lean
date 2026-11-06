import Mathlib

/- 16. Let $a, b, c \in \mathbf{R}^{+}$, prove: $a^{3}+b^{3}+c^{3}-3 a b c \geqslant \max \left\{(a-b)^{2} a,(a-b)^{2} b\right.$, $\left.(b-c)^{2} b,(b-c)^{2} c,(c-a)^{2} c,(c-a)^{2} a\right\} .(1999$ MOP Problem)-/
theorem inequalities_602771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ max (max (max (max (max ((a - b) ^ 2 * a) ((a - b) ^ 2 * b)) ((b - c) ^ 2 * b)) ((b - c) ^ 2 * c)) ((c - a) ^ 2 * c)) ((c - a) ^ 2 * a) := by
  -- Show a lemma that could be used multiple times later.
  have hlm (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ (a - b) ^ 2 * a := by
    -- We use the fact that (a - b)² + (b - c)² + (c - a)² ≥ 0.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Simplify use the above lemma for 6 times.
  iterate 5 apply max_le
  . specialize hlm a b c ha hb hc
    linarith
  . specialize hlm b a c hb ha hc
    linarith
  . specialize hlm b c a hb hc ha
    linarith
  . specialize hlm c b a hc hb ha
    linarith
  . specialize hlm c a b hc ha hb
    linarith
  . specialize hlm a c b ha hc hb
    linarith