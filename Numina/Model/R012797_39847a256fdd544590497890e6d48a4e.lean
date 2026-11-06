import Mathlib

open Real

theorem inequalities_108292 (K : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
      sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b) ≥
        K * sqrt (a + b + c)) ↔
    K ≤ sqrt 3 := by 
  constructor
  · -- Forward direction: if inequality holds, prove K <= sqrt(3)
    intro h
    have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have h2 : sqrt ((1 : ℝ) * (1 : ℝ) / (1 : ℝ)) = 1 := by
      simp [sqrt_eq_iff_sq_eq]
      <;> norm_num
    have h3 : sqrt ((1 + 1 + 1 : ℝ)) = Real.sqrt 3 := by norm_num
    simp only [h2, h3] at h1
    by_contra h'
    push_neg at h'
    have h6 : (sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, sq_nonneg (K - Real.sqrt 3), sq_nonneg (sqrt 3 ^ 2), h6]
  · -- Backward direction: if K <= sqrt(3), prove the inequality
    rintro h a b c ha hb hc
    have h1 : sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b) ≥ Real.sqrt 3 * Real.sqrt (a + b + c) := by
      have h2 : (sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b)) ^ 2 ≥ 3 * (a + b + c) := by
        have h3 : (sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b)) ^ 2
            = (sqrt (a * b / c)) ^ 2 + (sqrt (b * c / a)) ^ 2 + (sqrt (a * c / b)) ^ 2 + 2 * (sqrt (a * b / c) * sqrt (b * c / a) + sqrt (a * b / c) * sqrt (a * c / b) + sqrt (b * c / a) * sqrt (a * c / b)) := by
          ring
        have h4 : (sqrt (a * b / c)) ^ 2 = a * b / c := by
          rw [Real.sq_sqrt]
          positivity
        have h5 : (sqrt (b * c / a)) ^ 2 = b * c / a := by
          rw [Real.sq_sqrt]
          positivity
        have h6 : (sqrt (a * c / b)) ^ 2 = a * c / b := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (sqrt (a * b / c) * sqrt (b * c / a) ) = b := by
          have h9 : sqrt (a * b / c) * sqrt (b * c / a) = sqrt ((a * b / c) * (b * c / a)) := by
            rw [← Real.sqrt_mul (by positivity)]
            all_goals positivity
          rw [h9]
          have h10 : (a * b / c) * (b * c / a) = (b: ℝ) ^ 2 := by
            field_simp
            <;> nlinarith
            all_goals positivity
          rw [h10]
          have h11 : sqrt ((b: ℝ) ^ 2) = (b: ℝ) := by
            rw [Real.sqrt_sq (by positivity)]
          rw [h11]
          all_goals nlinarith
          all_goals positivity
        have h8 : (sqrt (a * b / c) * sqrt (a * c / b) ) = a := by
          have h12 : sqrt (a * b / c) * sqrt (a * c / b) = sqrt ((a * b / c) * (a * c / b)) := by
            rw [← Real.sqrt_mul (by positivity)]
            all_goals positivity
          rw [h12]
          have h13 : (a * b / c) * (a * c / b) = (a: ℝ) ^ 2 := by
            field_simp
            <;> nlinarith
            all_goals positivity
          rw [h13]
          have h14 : sqrt ((a: ℝ) ^ 2) = (a: ℝ) := by
            rw [Real.sqrt_sq (by positivity)]
          rw [h14]
          all_goals nlinarith
          all_goals positivity
        have h9 : (sqrt (b * c / a) * sqrt (a * c / b) ) = c := by
          have h15 : sqrt (b * c / a) * sqrt (a * c / b) = sqrt ((b * c / a) * (a * c / b)) := by
            rw [← Real.sqrt_mul (by positivity)]
            all_goals positivity
          rw [h15]
          have h16 : (b * c / a) * (a * c / b) = (c: ℝ) ^ 2 := by
            field_simp
            <;> nlinarith
            all_goals positivity
          rw [h16]
          have h17 : sqrt ((c: ℝ) ^ 2) = (c: ℝ) := by
            rw [Real.sqrt_sq (by positivity)]
          rw [h17]
          all_goals nlinarith
          all_goals positivity
        rw [h3, h4, h5, h6, h7, h8, h9]
        have h12 : a * b / c + b * c / a + a * c / b ≥ (a + b + c) := by
          have h14 : a * b / c + b * c / a + a * c / b - (a + b + c) ≥ 0 := by
            have h17 : a * b / c + b * c / a + a * c / b - (a + b + c) =
                (a^2 * b^2 + b^2 * c^2 + a^2 * c^2 - (a * b * c) * (a + b + c)) / (a * b * c) := by
              field_simp
              ring_nf
              <;> field_simp
              <;> ring
            rw [h17]
            have h18 : a * b * c > 0 := by positivity
            have h19 : (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) ≥ (a * b * c) * (a + b + c) := by
              nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
            have h20 : (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) - (a * b * c) * (a + b + c) ≥ 0 := by linarith
            have h21 : (a^2 * b^2 + b^2 * c^2 + a^2 * c^2 - (a * b * c) * (a + b + c)) / (a * b * c) ≥ 0 := by
              apply div_nonneg
              linarith
              all_goals positivity
            linarith
          linarith
        nlinarith [sq_nonneg (sqrt (a * b / c) - sqrt (b * c / a)), sq_nonneg (sqrt (a * b / c) - sqrt (a * c / b)), sq_nonneg (sqrt (b * c / a) - sqrt (a * c / b)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h3 : Real.sqrt (3 * (a + b + c)) = Real.sqrt 3 * Real.sqrt (a + b + c) := by
        have h4 : (3 * (a + b + c) : ℝ) = (3 : ℝ) * (a + b + c) := by ring
        rw [h4]
        have h6 : 0 ≤ (3 : ℝ) := by norm_num
        have h7 : 0 ≤ (a + b + c : ℝ) := by
          linarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
        rw [Real.sqrt_mul (by positivity)]
        all_goals positivity
      have h8 : Real.sqrt (3 * (a + b + c)) ^ 2 = 3 * (a + b + c) := by
        rw [Real.sq_sqrt]
        positivity
      have h9 : (sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b)) ^ 2 ≥ 3 * (a + b + c) := h2
      have h10 : 0 ≤ (sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b) : ℝ) := by positivity
      have h11 : Real.sqrt (3 * (a + b + c)) = Real.sqrt 3 * Real.sqrt (a + b + c) := h3
      have h12 : (sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b)) ≥ Real.sqrt (3 * (a + b + c)) := by
        nlinarith [Real.sqrt_nonneg (3 * (a + b + c)), Real.sqrt_nonneg 3, Real.sqrt_nonneg (a + b + c),
          Real.sq_sqrt (show 0 ≤ (3 * (a + b + c) : ℝ) by positivity)]
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (a + b + c)]
    nlinarith [show sqrt (a * b / c) + sqrt (b * c / a) + sqrt (a * c / b) ≥ 0 by positivity, h1, h, Real.sqrt_nonneg 3, Real.sqrt_nonneg (a + b + c)]