import Mathlib

open Real

theorem algebra_7561 :
    IsGreatest {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a * b = 1 ∧ x = 2 * (a ^ 3 + b ^ 3) / ((a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4))} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 1, 1
    norm_num
  · -- Show that 1 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hprod, hx⟩
    have h1 : (a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4) = a^6 + b^6 + 2 := by
      have h2 : a ^ 2 * b ^ 2 = 1 := by
        nlinarith [hprod, sq_nonneg (a * b - 1), mul_pos ha hb]
      have h3 : a ^ 4 * b ^ 4 = 1 := by
        have h31 : a ^ 2 * b ^ 2 = 1 := h2
        have h32 : (a ^ 2 * b ^ 2) ^ 2 = 1 := by
          rw [h31]
          all_goals norm_num
        nlinarith
      calc
        (a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4)
          = a^6 + a^4 * b^4 + a^2 * b^2 + b^6 := by
            ring_nf
        _ = a^6 + 1 + 1 + b^6 := by
          rw [show a^4 * b^4 = 1 by nlinarith [h3], show a^2 * b^2 = 1 by nlinarith [h2]]
          all_goals nlinarith
        _ = a^6 + b^6 + 2 := by
          ring_nf
    have h4 : 2 * (a ^ 3 + b ^ 3) ≤ (a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4) := by
      rw [h1]
      nlinarith [sq_nonneg (a ^ 3 - 1), sq_nonneg (b ^ 3 - 1), sq_nonneg (a - b), sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), 
        hprod, sq_nonneg (a * b - 1), mul_pos ha hb, mul_pos (show 0 < a by linarith) (show 0 < b by linarith)]
    have h5 : 2 * (a ^ 3 + b ^ 3) / ((a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4)) ≤ 1 := by
      have pos1 : (a ^ 4 + b ^ 2) * (a ^ 2 + b ^ 4) > 0 := by
        positivity
      apply (div_le_iff₀ pos1).mpr
      nlinarith [h4, hprod, mul_pos ha hb]
    linarith [hx, h5]