import Mathlib

theorem inequalities_235157 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ¬(a + b < c + d ∧ (a + b) * (c + d) < a * b + c * d ∧ (a + b) * c * d < a * b * (c + d)) := by
  intro h
  rcases h with ⟨h1, h2, h3⟩

  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          mul_self_nonneg (a - b), mul_self_nonneg (c - d),
          mul_self_nonneg (a + b - (c + d)), mul_self_nonneg (a * b - c * d),
          sq_nonneg (a - c), sq_nonneg (b - d),
          sq_nonneg (a*d - b*c)]