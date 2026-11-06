import Mathlib

/- For any positive numbers $a, b, c$ prove the inequalities

$$
\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \geq \frac{2}{a+b}+\frac{2}{b+c}+\frac{2}{c+a} \geq \frac{9}{a+b+c} .
$$ -/
theorem inequalities_237173 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≥ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ∧
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c) := by
  constructor
  . -- First, we show that 2 / (a + b) ≤ 1 / 2 * (1 / a + 1 / b)
    -- We have 2 / (a + b) ≤ 1 / 2 * (1 / a + 1 / b)
    have lem {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 2 / (a + b) ≤ 1 / 2 * (1 / a + 1 / b) := by
      -- After cancelling the denominators, it follows by completing the square
      field_simp
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [sq_nonneg (a - b)]
    -- Use the lemma for a, b; b, c; c, a
    have h1 := lem ha hb
    have h2 := lem hb hc
    have h3 := lem hc ha
    -- Add the inequalities
    linarith [h1, h2, h3]
  . -- Second, we show that 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c)
    -- Set x := a + b, y := b + c, z := c + a
    let x := a + b
    let y := b + c
    let z := c + a
    rw [show 9 / (a + b + c) = 18 / (x + y + z) by field_simp; ring]
    change 2 / x + 2 / y + 2 / z ≥ 18 / (x + y + z)
    -- The second inequality is equivalent to 1 / x + 1 / y + 1 / z ≥ 9 / (x + y + z)
    suffices 1 / x + 1 / y + 1 / z ≥ 9 / (x + y + z) by ring_nf at this ⊢; linarith only [this]
    -- We use Cauchy-Schwarz:
    -- (1 + 1 + 1) ^ 2 / (x + y + z) ≤ 1 ^ 2 / x + 1 ^ 2 / y + 1 ^ 2 / z
    have lem := Finset.sq_sum_div_le_sum_sq_div Finset.univ ![1, 1, 1] (g := ![x, y, z]) (by intro i; fin_cases i <;> simp <;> positivity)
    -- Now simplify both the goal and the lemma and we are done
    simp [Finset.sum] at lem
    ring_nf at lem ⊢
    linarith only [lem]
