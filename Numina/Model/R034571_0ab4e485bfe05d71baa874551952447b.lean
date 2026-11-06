import Mathlib

open Finset

theorem inequalities_132519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ∧
    (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ≤
    a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) := by
  constructor
  · -- Prove the first inequality: a + b + c ≤ (a^2 + b^2)/(2c) + (b^2 + c^2)/(2a) + (c^2 + a^2)/(2b)
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    have h2 : (a + b + c) ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) := by
      have pos1 : 0 < (2 * c) := by nlinarith
      have pos2 : 0 < (2 * a) := by nlinarith
      have pos3 : 0 < (2 * b) := by nlinarith
      have h3 : 0 < (2 * a * b * c) := by
        nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
      have h4 : (a + b + c) * (2 * a * b * c) ≤ (a ^ 2 + b ^ 2) * (a * b) + (b ^ 2 + c ^ 2) * (b * c) + (c ^ 2 + a ^ 2) * (a * c) := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h5 : (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) - (a + b + c) ≥ 0 := by
        have h7 : ((a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) - (a + b + c)) =
          (( (a ^ 2 + b ^ 2) * (a * b) + (b ^ 2 + c ^ 2) * (b * c) + (c ^ 2 + a ^ 2) * (a * c) - (a + b + c) * (2 * a * b * c)) / (2 * a * b * c)) := by 
          field_simp
          <;> ring
        rw [h7] at *
        apply div_nonneg
        linarith [h4]
        positivity
      linarith
    exact h2
  · -- Prove the second inequality: (a^2 + b^2)/(2c) + (b^2 + c^2)/(2a) + (c^2 + a^2)/(2b) ≤ a^3/(bc) + b^3/(ca) + c^3/(ab)
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    have h6 : (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ≤
      a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) := by
      have pos1 : 0 < (2 * a * b * c) := by
        nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
      have h7 : ( (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ) - ( a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ) ≤ 0 := by
        have h8 : ( (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ) - ( a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ) = (( (a ^ 2 + b ^ 2) * (a * b) + (b ^ 2 + c ^ 2) * (b * c) + (c ^ 2 + a ^ 2) * (a * c) ) - 2 * (a^4 + b^4 + c^4)) / (2 * a * b * c) := by 
          field_simp
          <;> ring
        rw [h8] at *
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show the numerator is non-positive
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
        · -- Show the denominator is non-negative
          positivity
      linarith
    exact h6