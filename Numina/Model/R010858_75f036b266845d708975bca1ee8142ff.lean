import Mathlib

theorem algebra_9240_v0001 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : b ^ 2 + 2 * (a + c) * b - a * c = 0) : b / (a + c) ≤ (Real.sqrt 5 - 2) / 2 ∧ ∃ a b c, b / (a + c) = (Real.sqrt 5 - 2) / 2 := by
  have h1 : 0 < a + c := by linarith
  have h2 : b ^ 2 + 2 * (a + c) * b = a * c := by linarith
  have h3 : a * c ≤ ( (a + c) / 2 ) ^ 2 := by
    nlinarith [sq_nonneg (a - c)]
  -- So $b^2 + 2(a + c)b \leq ((a + c)/2)^2$.
  have h4 : (b) ^ 2 + 2 * (a + c) * b ≤ ( (a + c) / 2 ) ^ 2 := by
    nlinarith [h2, h3]
  have h5 : b / (a + c) ≤ (Real.sqrt 5 - 2) / 2 := by
    have h6 : 0 < (a + c : ℝ) := by linarith
    have h7 : (b / (a + c)) ^ 2 + 2 * (b / (a + c)) ≤ 1 / 4 := by
      have h8 : (b) ^ 2 + 2 * (a + c) * b ≤ ( (a + c) / 2 ) ^ 2 := h4
      have h9 : (b) ^ 2 + 2 * (a + c) * b = (b / (a + c)) ^ 2 * (a + c) ^ 2 + 2 * (b / (a + c)) * (a + c) ^ 2 := by
        field_simp
        <;> nlinarith
      have h10 : ( (a + c) / 2 ) ^ 2 = (1 / 4) * (a + c) ^ 2 := by
        ring_nf
      rw [h9, h10] at h8
      have h11 : (a + c) ^ 2 > 0 := by positivity
      have h12 : (b / (a + c)) ^ 2 + 2 * (b / (a + c)) ≤ 1 / 4 := by
        nlinarith
      linarith
    -- Now, we solve the quadratic $k^2 + 2k -1/4 \leq 0$.
    -- Find the roots: $k = (-2 \pm \sqrt{4 + 1})/2 = (-2 \pm \sqrt{5})/2$.
    -- So the solutions between the roots: $(-2 - \sqrt{5})/2 \leq k \leq (-2 + \sqrt{5})/2$.
    -- Since $k > 0$, so $k \leq (-2 + \sqrt{5})/2 = (\sqrt{5}-2)/2$.
    have h8 : (b / (a + c) - (Real.sqrt 5 - 2) / 2) ≤ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by linarith : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith : (0 : ℝ) ≤ (5 : ℝ)), Real.sqrt_nonneg 5]
    linarith
  -- We now prove the second part: existence of values where equality holds.
  have h6 : ∃ a b c, b / (a + c) = (Real.sqrt 5 - 2) / 2 := by
    use 1, Real.sqrt 5 - 2, 1
    have hb1 : 0 < Real.sqrt 5 - 2 := by
      have h1 : 2 < Real.sqrt 5 := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    have hb2 : (Real.sqrt 5 - 2 : ℝ) / ((1 : ℝ) + (1 : ℝ)) = (Real.sqrt 5 - 2) / 2 := by
      norm_num
    linarith [hb2]
  -- Combine both parts.
  constructor
  · exact h5
  · exact h6