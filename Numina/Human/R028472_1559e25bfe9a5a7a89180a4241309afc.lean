import Mathlib

/- Let $0 \leqslant a, b, c, d, e \leqslant 1$ be real numbers. Prove that
$$
(1+a+b+c+d+e)^{2} \geqslant 4\left(a^{2}+b^{2}+c^{2}+d^{2}+e^{2}\right)
$$ -/
theorem inequalities_607623
    (a b c d e : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1)
    (he : 0 ≤ e ∧ e ≤ 1) :
    (1 + a + b + c + d + e)^2 ≥ 4 * (a^2 + b^2 + c^2 + d^2 + e^2) := by

  -- The idea is to use the inequality $(x+y)^{2} \geqslant 4 x y$ for $x=1$ and a specific value of $y$.
  have h1 (x y : ℝ) : (x + y) ^ 2 ≥ 4 * x * y := by
    -- More precisely, for all $x, y \geqslant 0$, we have $(x-y)^{2} \geqslant 0$, and thus $(x+y)^{2} \geqslant 4 x y$ (this inequality is also the AM-GM inequality for two variables).
    --suffices : (x - y) ^ 2 ≥ 0
    nlinarith [sq_nonneg (x - y)]

  -- By evaluating this inequality with $x=1$ and $y=a+b+c+d+e$, we obtain: $$ (1+a+b+c+d+e)^{2} \geqslant 4(a+b+c+d+e) $$
  specialize h1 1 (a + b + c + d + e)
  simp_rw [← add_assoc, mul_one] at h1

  -- For any real number $x$ such that $0 \leqslant x \leqslant 1$, we have  $x \geqslant x^{2}$ . Therefore, $$ 4(a+b+c+d+e) \geqslant 4\left(a^{2}+b^{2}+c^{2}+d^{2}+e^{2}\right) $$
  have h2 : 4 * (a + b + c + d + e) ≥ 4 * (a^2 + b^2 + c^2 + d^2 + e^2) := by
    have {x : ℝ} : 0 ≤ x ∧ x ≤ 1 → x ≥ x ^ 2 := by
      intro hx
      nlinarith
    gcongr
    <;> simp_all

  -- This ultimately shows that: $$ 4(a+b+c+d+e) \geqslant 4\left(a^{2}+b^{2}+c^{2}+d^{2}+e^{2}\right) $$
  linarith only [h1, h2]
