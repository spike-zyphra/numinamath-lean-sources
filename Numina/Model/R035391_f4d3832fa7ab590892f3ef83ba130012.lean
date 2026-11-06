import Mathlib

open Real
open scoped BigOperators

theorem inequalities_88107 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  let s := (1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b)))
  s ≤ (a^2 + b^2 + c^2)/6 := by
  intro s
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : -1 ≤ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) := by
    have h2 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≥ -1 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
    linarith
  have h3 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 := by
    have h3 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
    linarith
  have h4 : -1 ≤ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ∧ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 := ⟨h2, h3⟩
  have h5 : sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b))) = Real.sqrt (1 - ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2) := by
    rw [sin_arccos]
    all_goals
      have h4' : -1 ≤ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ∧ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 := h4
      all_goals
        try { linarith [h4'.1, h4'.2] }
  have h6 : s ≤ (a^2 + b^2 + c^2)/6 := by
    have h7 : s = (1/4) * Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) := by
      have h8 : s = (1/2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b)) ^ 2) := by
        rw [show s = (1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b))) by rfl]
        rw [h5]
      have h9 : (1/2 : ℝ) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b)) ^ 2) = (1/4) * Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) := by
        have h10 : 0 < (2 * a * b) := by positivity
        have h11 : Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b)) ^ 2) = Real.sqrt ((4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / (4 * a^2 * b^2)) := by
          have h12 : (1 - ((a^2 + b^2 - c^2) / (2 * a * b)) ^ 2 : ℝ) = (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / (4 * a^2 * b^2) := by
            field_simp
            ring_nf
          rw [h12]
        rw [h11]
        have h12 : Real.sqrt ((4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / (4 * a^2 * b^2)) = Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / (2 * a * b) := by
          have h13 : (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2 : ℝ) ≥ 0 := by
            nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
              mul_pos (sub_pos.2 h) (sub_pos.2 h'), mul_pos (sub_pos.2 h') (sub_pos.2 h''), mul_pos (sub_pos.2 h'') (sub_pos.2 h)]
          have h14 : Real.sqrt ((4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / (4 * a^2 * b^2)) = Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) / Real.sqrt (4 * a^2 * b^2) := by
            rw [Real.sqrt_div (by nlinarith)]
          have h15 : Real.sqrt (4 * a^2 * b^2) = 2 * a * b := by
            have h16 : (4 * a^2 * b^2 : ℝ) = (2 * a * b) ^ 2 := by
              ring
            rw [h16]
            have h17 : 0 ≤ (2 * a * b : ℝ) := by positivity
            rw [Real.sqrt_sq (by positivity)]
          rw [h14, h15]
        rw [h12]
        field_simp
        all_goals ring_nf
      linarith [h9]
    rw [h7]
    have h16 : Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) ≤ 2 * (a^2 + b^2 + c^2) / 3 := by
      have h13 : (Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2)) ^ 2 = 4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (sub_pos.2 h) (sub_pos.2 h'), mul_pos (sub_pos.2 h') (sub_pos.2 h''), mul_pos (sub_pos.2 h'') (sub_pos.2 h)]
      have h14 : (2 * (a^2 + b^2 + c^2) / 3) ^ 2 ≥ (Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2)) ^ 2 := by
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (sub_pos.2 h) (sub_pos.2 h'), mul_pos (sub_pos.2 h') (sub_pos.2 h''), mul_pos (sub_pos.2 h'') (sub_pos.2 h),
          sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]
      have h15 : Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) ≥ 0 := by positivity
      have h16 : (2 * (a^2 + b^2 + c^2) / 3) ≥ Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) := by
        nlinarith [Real.sqrt_nonneg (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2), h13, sq_nonneg (2 * (a^2 + b^2 + c^2) / 3 - Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2)), sq_nonneg (2 * (a^2 + b^2 + c^2) / 3), sq_nonneg (Real.sqrt (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2)), h14]
      linarith
    nlinarith [Real.sqrt_nonneg (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2)]
  linarith