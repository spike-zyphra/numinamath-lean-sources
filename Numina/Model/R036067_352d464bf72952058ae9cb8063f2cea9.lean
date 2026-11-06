import Mathlib

open Real

theorem inequalities_312672 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    9 / 4 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ∧
    1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≤ 5 / 2 := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  
  constructor
  · -- Prove the lower bound: 9/4 ≤ S
    have h6 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 9 / 4 := by 
      have h8 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
      have h9 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4 ≥ 0 := by
        have h9 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 9 / 4 =
            ((1 + b) * (1 + c) + (1 + a) * (1 + c) + (1 + a) * (1 + b) - (9 / 4) * (1 + a) * (1 + b) * (1 + c)) / ((1 + a) * (1 + b) * (1 + c)) := by
          field_simp [show 0 < 1 + a by linarith, show 0 < 1 + b by linarith, show 0 < 1 + c by linarith]
          ring
        rw [h9]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
                  hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
        positivity
      linarith
    linarith
  
  · -- Prove the upper bound: S ≤ 5/2
    have h10 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≤ 5 / 2 := by 
      -- Need to clear denominators
      have h8 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
      have h9 : (5 / 2) - (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) =
          ((5 / 2) * (1 + a) * (1 + b) * (1 + c) - ((1 + b) * (1 + c) + (1 + a) * (1 + c) + (1 + a) * (1 + b))) / ((1 + a) * (1 + b) * (1 + c)) := by
        field_simp [show 0 < 1 + a by linarith, show 0 < 1 + b by linarith, show 0 < 1 + c by linarith]
        ring
      have h10 : ((5 / 2) * (1 + a) * (1 + b) * (1 + c) - ((1 + b) * (1 + c) + (1 + a) * (1 + c) + (1 + a) * (1 + b))) ≥ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
      have h11 : ((5 / 2) * (1 + a) * (1 + b) * (1 + c) - ((1 + b) * (1 + c) + (1 + a) * (1 + c) + (1 + a) * (1 + b)) ) / ((1 + a) * (1 + b) * (1 + c)) ≥ 0 := by 
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  all_goals linarith