import Mathlib

open Real

theorem inequalities_600395 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (lambda : ℝ) (hlambda : -2 < lambda ∧ lambda < 2) :
    sqrt (a^2 + lambda * a * b + b^2) +
    sqrt (b^2 + lambda * b * c + c^2) +
    sqrt (c^2 + lambda * c * a + a^2) ≥
    sqrt (2 + lambda) * (a + b + c) := by
  have h1 : -2 < lambda := hlambda.1
  have h2 : lambda < 2 := hlambda.2

  have h4 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      sqrt (a^2 + lambda * a * b + b^2) ≥ sqrt (2 + lambda) * (a + b) / 2 := by
    have h5 : sqrt (a^2 + lambda * a * b + b^2) ≥ sqrt (2 + lambda) * (a + b) / 2 := by
      have h6 : 0 ≤ (2 + lambda : ℝ) := by
        linarith
      have h7 : 2 + lambda > 0 := by
        linarith
      have h8 : (sqrt (2 + lambda) * (a + b) / 2) ^ 2 ≤ a^2 + lambda * a * b + b^2 := by
        have h9 : (sqrt (2 + lambda) * (a + b) / 2) ^ 2 = (2 + lambda) * ((a + b) / 2) ^ 2 := by
          calc
            (sqrt (2 + lambda) * (a + b) / 2) ^ 2 = (sqrt (2 + lambda) ^ 2) * ((a + b) / 2) ^ 2 := by ring_nf
            _ = (2 + lambda) * ((a + b) / 2) ^ 2 := by 
              rw [Real.sq_sqrt]
              linarith
        rw [h9]
        nlinarith [sq_nonneg (a - b), sq_nonneg (lambda), sq_nonneg (a + b), sq_nonneg (a - b),
          sq_nonneg (lambda * a - lambda * b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a - b)]
      have h12 : (sqrt (a^2 + lambda * a * b + b^2)) ^ 2 ≥ (sqrt (2 + lambda) * (a + b) / 2) ^ 2 := by
        have h13 : (sqrt (a^2 + lambda * a * b + b^2)) ^ 2 = a^2 + lambda * a * b + b^2 := by 
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (lambda), sq_nonneg (a * b)]
        have h14 : (sqrt (2 + lambda) * (a + b) / 2) ^ 2 = (2 + lambda) * ((a + b) / 2) ^ 2 := by
          calc
            (sqrt (2 + lambda) * (a + b) / 2) ^ 2 = (sqrt (2 + lambda) ^ 2) * ((a + b) / 2) ^ 2 := by ring_nf
            _ = (2 + lambda) * ((a + b) / 2) ^ 2 := by
              rw [Real.sq_sqrt]
              linarith
        nlinarith [sq_nonneg (sqrt (a^2 + lambda * a * b + b^2) - sqrt (2 + lambda) * (a + b) / 2), Real.sqrt_nonneg (2 + lambda), Real.sqrt_nonneg (a^2 + lambda * a * b + b^2), h8, sq_nonneg (a + b)]
      have h15 : sqrt (a^2 + lambda * a * b + b^2) ≥ sqrt (2 + lambda) * (a + b) / 2 := by
        nlinarith [Real.sqrt_nonneg (2 + lambda), Real.sqrt_nonneg (a^2 + lambda * a * b + b^2), h12, sq_nonneg (sqrt (2 + lambda) * (a + b) / 2 - sqrt (a^2 + lambda * a * b + b^2))]
      linarith
    linarith
  have h4a := h4 ha hb
  have h4b := h4 hb hc
  have h4c := h4 hc ha
  have h10 : sqrt (a^2 + lambda * a * b + b^2) +
      sqrt (b^2 + lambda * b * c + c^2) + sqrt (c^2 + lambda * c * a + a^2) ≥
      sqrt (2 + lambda) * (a + b + c) := by
    have h11 : sqrt (a^2 + lambda * a * b + b^2) ≥ sqrt (2 + lambda) * (a + b) / 2 := h4a
    have h12 : sqrt (b^2 + lambda * b * c + c^2) ≥ sqrt (2 + lambda) * (b + c) / 2 := h4b
    have h13 : sqrt (c^2 + lambda * c * a + a^2) ≥ sqrt (2 + lambda) * (c + a) / 2 := h4c
    have h14 : sqrt (2 + lambda) * (a + b) / 2 + sqrt (2 + lambda) * (b + c) / 2 + sqrt (2 + lambda) * (c + a) / 2 = sqrt (2 + lambda) * (a + b + c) := by
      ring_nf
    linarith [h11, h12, h13, h14, sq_nonneg (sqrt (2 + lambda) * (a + b + c) - (sqrt (a^2 + lambda * a * b + b^2) + sqrt (b^2 + lambda * b * c + c^2) + sqrt (c^2 + lambda * c * a + a^2)))
        ]
  linarith