import Mathlib

/- Prove that $\frac{a^{2}-b c}{2 a^{2}+b c}+\frac{b^{2}-c a}{2 b^{2}+c a}+\frac{c^{2}-a b}{2 c^{2}+a b} \leq 0$ for any real positive numbers $a, b, c$. -/
theorem inequalities_604445 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) +
    (c^2 - a * b) / (2 * c^2 + a * b) ≤ 0 := by
  -- Rewrite (a ^ 2 - b * c) / (2 * a^2 + b * c) as (1 - 3 * (b * c / (2 * a^2 + b * c))) / 2, and we can simplify the problem.
  -- It suffices to prove that b * c / (2 * a^2 + b * c) + c * a / (2 * b^2 + c * a) + a * b / (2 * c^2 + a * b) ≥ 1.
  suffices H : b * c / (2 * a^2 + b * c) + c * a / (2 * b^2 + c * a) + a * b / (2 * c^2 + a * b) ≥ 1 by
    have h₁ : (a ^ 2 - b * c) / (2 * a ^ 2 + b * c) = (1 - 3 * (b * c / (2 * a^2 + b * c))) / 2 := by
      field_simp [ha, hb, hc]
      ring
    have h₂ : (b ^ 2 - c * a) / (2 * b ^ 2 + c * a) = (1 - 3 * (c * a / (2 * b^2 + c * a))) / 2 := by
      field_simp [ha, hb, hc]
      ring
    have h₃ : (c ^ 2 - a * b) / (2 * c ^ 2 + a * b) = (1 - 3 * (a * b / (2 * c^2 + a * b))) / 2 := by
      field_simp [ha, hb, hc]
      ring
    rw [h₁, h₂, h₃]
    linarith only [H]
  -- We use Cauchy-Schwarz inequality to prove the result.
  -- Let f be the array [b * c, c * a, a * b], and g be the array [b * c * (2 * a^2 + b * c), c * a * (2 * b^2 + c * a), a * b * (2 * c^2 + a * b)].
  let s : Finset (Fin 3) := Finset.univ
  let f := ![b * c, c * a, a * b]
  let g := ![b * c * (2 * a^2 + b * c), c * a * (2 * b^2 + c * a), a * b * (2 * c^2 + a * b)]
  calc
    -- LHS = ∑ i ∈ s, f i ^ 2 / g i
    _ = ∑ i ∈ s, f i ^ 2 / g i := by
      simp [s, Finset.sum, Fin.succ, f, g]
      field_simp
      ring
    -- ≥ (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i, by Cauchy-Schwarz inequality
    _ ≥ (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i := by
      refine Finset.sq_sum_div_le_sum_sq_div s f ?_
      intro i
      simp [s, g]
      fin_cases i
      all_goals
        simp
        positivity
    -- = 1, by direct computation
    _ = 1 := by
      simp [s, Finset.sum, Fin.succ, f, g]
      field_simp
      ring
