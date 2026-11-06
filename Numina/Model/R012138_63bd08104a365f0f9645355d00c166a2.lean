import Mathlib

theorem inequalities_88545 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) *
    (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) *
    (c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1) ≥
    8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
  have h2 : a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = (a ^ 2 + a + 1) * (a ^ 3 + 1) := by 
    ring_nf

  have h3 : b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1 = (b ^ 2 + b + 1) * (b ^ 3 + 1) := by 
    ring_nf

  have h4 : c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = (c ^ 2 + c + 1) * (c ^ 3 + 1) := by 
    ring_nf

  rw [h2, h3, h4]
  have h5 : (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) ≥ 8 := by
    have h6 : a * b * c = 1 := habc
    -- derivatives
    -- Let x := a^3, y := b^3, z := c^3
    have hx : a^3 ≥ 0 := by positivity
    have hy : b^3 ≥ 0 := by positivity
    have hz : c^3 ≥ 0 := by positivity
    -- zero step is to express x * y * z = 1
    have h7' : a^3 * b^3 * c^3 = 1 := by
      calc
        a^3 * b^3 * c^3 = (a * b * c)^3 := by
          ring_nf
        _ = 1^3 := by
          rw [h6]
        _ = 1 := by
          norm_num

    -- first step is to exfand the expression 
    -- but by step need to a^3 * 1 *1 / (sim subgroup stated)  to access linear expansion step
    have h8 : (a^3 + 1) * (b^3 + 1) * (c^3 + 1) =
        1 + (a^3 * b^3 + a^3 * c^3 + b^3 * c^3) + (a^3 + b^3 + c^3) + 1 := by
      have h8' : (a^3 + 1) * (b^3 + 1) * (c^3 + 1) =
          a^3 * b^3 * c^3 + a^3 * b^3 + a^3 * c^3 + b^3 * c^3 + a^3 + b^3 + c^3 + 1 := by 
        ring_nf
      rw [h8']
      rw [h7']
      <;> nlinarith

    rw [h8]
    -- Positivity Squared substitutions to derive the zero roots in coordinates
    -- nonlinear expansions leads proof which squares root negative fact squaring relates in proofs to establish
    -- nonlinear wait which Expans are more values derived Cross derivda by the data reduction positive deriv 
    -- solutions as positive proven lists.
    nlinarith [sq_nonneg (a^3 * b^3 - 1), sq_nonneg (a^3 * c^3 - 1), sq_nonneg (b^3 * c^3 - 1), 
          sq_nonneg (a^3 - 1), sq_nonneg (b^3 - 1), sq_nonneg (c^3 - 1),
          mul_nonneg (show (0 : ℝ) ≤ a^3 by positivity) (show (0 : ℝ) ≤ b^3 by positivity),
          mul_nonneg (show (0 : ℝ) ≤ a^3 by positivity) (show (0 : ℝ) ≤ c^3 by positivity),
          mul_nonneg (show (0 : ℝ) ≤ b^3 by positivity) (show (0 : ℝ) ≤ c^3 by positivity),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]

  have h6 : ( (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) ) > 0 := by
    positivity

  nlinarith [h5, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]