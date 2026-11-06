import Mathlib

open Real

lemma lemma_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 ≤ a / (b / 2 + c) + b / (c / 2 + a) + c / (a / 2 + b) := by
  have h1 : 0 < b / 2 + c := by positivity
  have h2 : 0 < c / 2 + a := by positivity
  have h3 : 0 < a / 2 + b := by positivity
  have h4 : a / (b / 2 + c) + b / (c / 2 + a) + c / (a / 2 + b) - 2 ≥ 0 := by
    have h6 : a / (b / 2 + c) + b / (c / 2 + a) + c / (a / 2 + b) - 2 =
        (a * (c / 2 + a) * (a / 2 + b) + b * (b / 2 + c) * (a / 2 + b) + c * (b / 2 + c) * (c / 2 + a) - 2 * (b / 2 + c) * (c / 2 + a) * (a / 2 + b)) /
        ((b / 2 + c) * (c / 2 + a) * (a / 2 + b)) := by
      field_simp
      <;> ring
    rw [h6]
    have h7 : a * (c / 2 + a) * (a / 2 + b) + b * (b / 2 + c) * (a / 2 + b) + c * (b / 2 + c) * (c / 2 + a) - 2 * (b / 2 + c) * (c / 2 + a) * (a / 2 + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg
    .
      linarith
    all_goals positivity
  linarith


theorem inequalities_321125 (a b c lambda : ℝ) (h₀ : 0 < lambda) (h₁ : lambda ≤ a) (h₂ : lambda ≤ b) (h₃ : lambda ≤ c) :
    2 ≤ a / (sqrt (lambda * b - lambda ^ 2) + c) + b / (sqrt (lambda * c - lambda ^ 2) + a) +
        c / (sqrt (lambda * a - lambda ^ 2) + b) := by
  have ha1 : 0 < a := by nlinarith
  have hb1 : 0 < b := by nlinarith
  have hc1 : 0 < c := by nlinarith
  have h4 : lambda * b - lambda ^ 2 ≥ 0 := by nlinarith
  have h5 : lambda * c - lambda ^ 2 ≥ 0 := by nlinarith
  have h6 : lambda * a - lambda ^ 2 ≥ 0 := by nlinarith

  have h7 : sqrt (lambda * b - lambda ^ 2) ≤ b / 2 := by
    have h8 : sqrt (lambda * b - lambda ^ 2) = sqrt (lambda * (b - lambda)) := by ring_nf
    rw [h8]
    have h9 : lambda ≥ 0 := by linarith
    have h10 : b - lambda ≥ 0 := by nlinarith
    have h11 : sqrt (lambda * (b - lambda)) ≤ (lambda + (b - lambda)) / 2 := by
      nlinarith [sq_nonneg (sqrt (lambda * (b - lambda)) - (lambda + (b - lambda)) / 2),
          Real.sqrt_nonneg (lambda * (b - lambda)), Real.sq_sqrt (show 0 ≤ lambda * (b - lambda) by nlinarith),
          sq_nonneg (lambda - (b - lambda)), sq_nonneg (sqrt (lambda * (b - lambda)) ^ 2 - (lambda * (b - lambda)) ) ]
    have h12 : (lambda + (b - lambda)) / 2 = b / 2 := by ring_nf
    nlinarith

  have h8 : sqrt (lambda * c - lambda ^ 2) ≤ c / 2 := by
    have h9 : sqrt (lambda * c - lambda ^ 2) = sqrt (lambda * (c - lambda)) := by ring_nf
    rw [h9]
    have h10 : lambda ≥ 0 := by linarith
    have h11 : c - lambda ≥ 0 := by nlinarith
    have h12 : sqrt (lambda * (c - lambda)) ≤ (lambda + (c - lambda)) / 2 := by
      nlinarith [sq_nonneg (sqrt (lambda * (c - lambda)) - (lambda + (c - lambda)) / 2),
          Real.sqrt_nonneg (lambda * (c - lambda)), Real.sq_sqrt (show 0 ≤ lambda * (c - lambda) by nlinarith),
          sq_nonneg (lambda - (c - lambda)), sq_nonneg (sqrt (lambda * (c - lambda)) ^ 2 - (lambda * (c - lambda)) ) ]
    have h13 : (lambda + (c - lambda)) / 2 = c / 2 := by ring_nf
    nlinarith

  have h9 : sqrt (lambda * a - lambda ^ 2) ≤ a / 2 := by
    have h10 : sqrt (lambda * a - lambda ^ 2) = sqrt (lambda * (a - lambda)) := by ring_nf
    rw [h10]
    have h11 : lambda ≥ 0 := by linarith
    have h12 : a - lambda ≥ 0 := by nlinarith
    have h13 : sqrt (lambda * (a - lambda)) ≤ (lambda + (a - lambda)) / 2 := by
      nlinarith [sq_nonneg (sqrt (lambda * (a - lambda)) - (lambda + (a - lambda)) / 2),
          Real.sqrt_nonneg (lambda * (a - lambda)), Real.sq_sqrt (show 0 ≤ lambda * (a - lambda) by nlinarith),
          sq_nonneg (lambda - (a - lambda)), sq_nonneg (sqrt (lambda * (a - lambda)) ^ 2 - (lambda * (a - lambda)) ) ]
    have h14 : (lambda + (a - lambda)) / 2 = a / 2 := by ring_nf
    nlinarith

  have h13 : a / (sqrt (lambda * b - lambda ^ 2) + c) ≥ a / (b / 2 + c) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h7]

  have h14 : b / (sqrt (lambda * c - lambda ^ 2) + a) ≥ b / (c / 2 + a) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h8]

  have h15 : c / (sqrt (lambda * a - lambda ^ 2) + b) ≥ c / (a / 2 + b) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h9]

  have h16 : a / (sqrt (lambda * b - lambda ^ 2) + c) + b / (sqrt (lambda * c - lambda ^ 2) + a) + c / (sqrt (lambda * a - lambda ^ 2) + b) ≥
      a / (b / 2 + c) + b / (c / 2 + a) + c / (a / 2 + b) := by 
    linarith [h13, h14, h15]

  have h17 : 2 ≤ a / (b / 2 + c) + b / (c / 2 + a) + c / (a / 2 + b) := lemma_1 a b c ha1 hb1 hc1
  linarith [h16, h17]