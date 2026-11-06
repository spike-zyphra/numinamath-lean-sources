import Mathlib

open Real Set

theorem algebra_281584 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    a / (1 + b) + b / (1 + a) + (1 - a) * (1 - b) ≤ 1 ∧
    a / (1 + b) + b / (1 + a) + (1 - a) * (1 - b) ≥ 0 := by
  have ha1 : 0 ≤ a := ha.1
  have ha2 : a ≤ 1 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b ≤ 1 := hb.2
  constructor
  · -- First prove $S \leq 1$.
    have h1 : 0 < (1 + a) * (1 + b) := by
      positivity
    have h2 : a / (1 + b) + b / (1 + a) + (1 - a) * (1 - b) - 1 ≤ 0 := by
      have h3 : a / (1 + b) + b / (1 + a) + (1 - a) * (1 - b) - 1 =
          (a * (1 + a) + b * (1 + b) - a * (1 + a) * (1 + b) - b * (1 + b) * (1 + a) + a * b * (1 + a) * (1 + b)) / ((1 + b) * (1 + a)) := by
        field_simp [(show 0 < 1 + a by linarith), (show 0 < 1 + b by linarith)]
        ring
      rw [h3] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Prove the numerator is ≤ 0
        nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2),
          mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - a by linarith),
          sq_nonneg (a - b), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2)]
      · -- Prove the denominator is ≥ 0
        positivity
    linarith
  · -- Prove $S \geq 0$.
    have h41 : a / (1 + b) ≥ 0 := by
      apply div_nonneg
      linarith 
      linarith 
    have h42 : b / (1 + a) ≥ 0 := by 
      apply div_nonneg
      linarith 
      linarith 
    have h43 : (1 - a) * (1 - b) ≥ 0 := by
      have h11 : 0 ≤ 1 - a := by linarith
      have h12 : 0 ≤ 1 - b := by linarith
      nlinarith
    linarith