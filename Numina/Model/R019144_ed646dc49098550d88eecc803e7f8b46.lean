import Mathlib

theorem inequalities_62705 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ∧
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≤ 1 / a + 1 / b + 1 / c := by
  constructor
  · -- Prove the left inequality: 9/(a+b+c) ≤ 2/(a+b) + 2/(b+c) + 2/(c+a)
    have h1 : 0 < a + b := by linarith
    have h2 : 0 < b + c := by linarith
    have h3 : 0 < c + a := by linarith
    have h4 : 0 < a + b + c := by linarith
    have h5 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) ≥ 0 := by
      have h6 : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by positivity
      have h7 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) =
          (2 * (b + c) * (c + a) * (a + b + c) + 2 * (a + b) * (c + a) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a) * (a + b + c)) := by
        field_simp
        ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        mul_pos (show 0 < a + b by linarith) (show 0 < a + c by linarith),
        mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith),
        mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith)]
      all_goals positivity
    linarith
  · -- Prove the right inequality: 2/(a + b) + 2/(b + c) + 2/(c + a) ≤ 1/a + 1/b + 1/c
    have h1 : 0 < a := ha
    have h2 : 0 < b := hb
    have h3 : 0 < c := hc
    have h4 : 0 < a * b * c := by
      positivity
    -- First, proving the key inequality: $ \frac{1}{a} + \frac{1}{b} \geq \frac{4}{a + b} $
    have h5 : 1 / a + 1 / b ≥ 4 / (a + b) := by
      have h6 : 0 < a + b := by linarith
      -- Using the property that $(a + b)^2 \geq 4ab$
      have h7 : (a + b) ^ 2 ≥ 4 * (a * b) := by
        nlinarith [sq_nonneg (a - b)]
      have h8 : 1 / a + 1 / b - 4 / (a + b) ≥ 0 := by
        have h12 : 0 < a := by linarith
        have h13 : 0 < b := by linarith
        have h14 : 0 < a + b := by linarith
        have h15 : 1 / a + 1 / b - 4 / (a + b) = ((a + b) ^ 2 - 4 * (a * b)) / (a * b * (a + b)) := by
          field_simp
          ring
        rw [h15]
        apply div_nonneg
        linarith [h7]
        positivity
      linarith
    -- Similarly, proving $ \frac{1}{b} + \frac{1}{c} \geq \frac{4}{b + c} $
    have h8 : 1 / b + 1 / c ≥ 4 / (b + c) := by
      have h9 : 0 < b := hb
      have h10 : 0 < c := hc
      have h11 : 0 < b + c := by linarith
      have h12 : (b + c) ^ 2 ≥ 4 * (b * c) := by
        nlinarith [sq_nonneg (b - c)]
      have h14 : 1 / b + 1 / c - 4 / (b + c) ≥ 0 := by
        have h15 : 1 / b + 1 / c - 4 / (b + c) = ((b + c) ^ 2 - 4 * (b * c)) / (b * c * (b + c)) := by
          field_simp
          ring
        rw [h15]
        apply div_nonneg
        linarith [h12]
        positivity
      linarith
    -- Similarly, proving $ \frac{1}{c} + \frac{1}{a} \geq \frac{4}{c + a} $
    have h11 : 1 / c + 1 / a ≥ 4 / (c + a) := by
      have h12 : 0 < c := hc
      have h13 : 0 < a := ha
      have h14 : 0 < c + a := by linarith
      have h15 : (c + a) ^ 2 ≥ 4 * (c * a) := by
        nlinarith [sq_nonneg (c - a)]
      have h17 : 1 / c + 1 / a - 4 / (c + a) ≥ 0 := by
        have h18 : 1 / c + 1 / a - 4 / (c + a) = ((c + a) ^ 2 - 4 * (c * a)) / (c * a * (c + a)) := by
          field_simp
          ring
        rw [h18]
        apply div_nonneg
        linarith [h15]
        positivity
      linarith
    -- Adding the three proven inequalities
    have h14 : 1 / a + 1 / b + 1 / c - (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 0 := by
      have h17 : 1 / a + 1 / b + 1 / c - (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) = 
        ( (1 / a + 1 / b) - 4 / (a + b) ) / 2 + ( (1 / b + 1 / c) - 4 / (b + c) ) / 2 + ( (1 / c + 1 / a) - 4 / (c + a) ) / 2 := by
        field_simp
        ring
      rw [h17]
      have h18 : ( (1 / a + 1 / b) - 4 / (a + b) ) / 2 ≥ 0 := by
        linarith [h5]
      have h19 : ( (1 / b + 1 / c) - 4 / (b + c) ) / 2 ≥ 0 := by
        linarith [h8]
      have h20 : ( (1 / c + 1 / a) - 4 / (c + a) ) / 2 ≥ 0 := by
        linarith [h11]
      linarith
    linarith