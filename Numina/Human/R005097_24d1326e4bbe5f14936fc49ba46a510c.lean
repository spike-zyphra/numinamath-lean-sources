import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that

$$
\frac{2 a}{a^{2}+b c}+\frac{2 b}{b^{2}+c a}+\frac{2 c}{c^{2}+a b} \leq \frac{a}{b c}+\frac{b}{c a}+\frac{c}{a b} .
$$ -/
theorem inequalities_605500
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2*a/(a^2+b*c) + 2*b/(b^2+c*a) + 2*c/(c^2+a*b) ≤ a/(b*c) + b/(c*a) + c/(a*b) := by

  -- First we prove that $$ \frac{2 a}{a^{2}+b c} \leq \frac{1}{2}\left(\frac{1}{b}+\frac{1}{c}\right) $$
  -- notice that we use new variable a, b c, to be generalized for b c a and c a b
  have r1 {a b c : ℝ} : 0 < a → 0 < b → 0 < c → 2*a/(a^2+b*c) ≤ 1/2 * (1/b + 1/c) := by
    intro ha hb hc
    -- it is equivalent to $0 \leq b(a-c)^{2}+c(a-b)^{2}$, and therefore holds true.
    suffices : 0 ≤ b * (a - c) ^ 2 + c * (a - b) ^ 2
    . rw [show 1/2 * (1/b + 1/c) = (b + c) / (2 * b * c) by field_simp; ring]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith only [this]
    positivity

  -- Now we turn to the inequality $$ \frac{1}{b}+\frac{1}{c} \leq \frac{1}{2}\left(\frac{2 a}{b c}+\frac{b}{c a}+\frac{c}{a b}\right), $$
  have r2 {a b c : ℝ} : 0 < a → 0 < b → 0 < c → 1/b + 1/c ≤ 1/2 * (2*a/(b*c) + b/(c*a) + c/(a*b)) := by
    intro ha hb hc
    -- which by multiplying by $2 a b c$ is seen to be equivalent to $0 \leq(a-b)^{2}+(a-c)^{2}$. Hence we have proved that
    suffices : 0 ≤ (a - b) ^ 2 + (a - c) ^ 2
    . refine le_of_mul_le_mul_right ?_ (show 0 < 2 * a * b * c by positivity)
      rw [show (1 / b + 1 / c) * (2 * a * b * c) = 2 * a * c + 2 * a * b by field_simp; ring_nf,
          show 1 / 2 * (2 * a / (b * c) + b / (c * a) + c / (a * b)) * (2 * a * b * c) = 2 * a ^ 2 + b ^ 2 + c ^ 2 by field_simp; ring_nf]
      linarith only [this]
    positivity

  -- Analogously we have $$ \frac{2 a}{a^{2}+b c} \leq \frac{1}{4}\left(\frac{2 a}{b c}+\frac{b}{c a}+\frac{c}{a b}\right) . $$
  have r3 {a b c : ℝ} : 0 < a → 0 < b → 0 < c → 2*a/(a^2+b*c) ≤ 1/4 * (2*a/(b*c) + b/(c*a) + c/(a*b)) := by
    intro ha hb hc
    linarith only [r1 ha hb hc, r2 ha hb hc]

  have rabc := r3 ha hb hc
  have rbca := r3 hb hc ha
  have rcab := r3 hc ha hb

  -- and it suffices to sum the above three inequalities.
  ring_nf at rabc rbca rcab
  ring_nf
  linarith