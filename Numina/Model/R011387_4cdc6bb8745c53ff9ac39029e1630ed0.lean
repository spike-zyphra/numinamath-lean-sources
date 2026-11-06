import Mathlib

theorem inequalities_112767 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (a + c) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by

  have h1 {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
      2 * (u * v) / (u + v) ≤ (u + v) / 2 := by
    have h2 : 0 < (u + v) := by linarith
    have h3 : 2 * (u * v) ≤ (u + v) * (u + v) / 2 := by
      have h4 : (u - v) ^ 2 ≥ 0 := sq_nonneg (u - v)
      nlinarith [sq_nonneg (u - v)]
    have h4 : 2 * (u * v) / (u + v) ≤ (u + v) / 2 := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    linarith

  have h2 {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (huvw : u * v * w = 1) :
      1 / (u + v) ≤ (u + v) * w / 4 := by
    have h3 : 1 / (u + v) ≤ (u + v) * w / 4 := by
      have h4 : 0 < (u + v) := add_pos hu hv
      have h5 : 0 < 4 * (u + v) := by positivity
      have h7 : u * v * w = 1 := by exact huvw
      have h9 : w = 1 / (u * v) := by
        have h14 : u * v ≠ 0 := mul_ne_zero (ne_of_gt hu) (ne_of_gt hv)
        field_simp
        nlinarith [huvw]
      have h10 : (u + v) * w / 4 ≥ 1 / (u + v) := by
        have h11 : 0 < (u + v) := by positivity
        have h14 : 0 < (u * v) := mul_pos hu hv
        have h13 : (u + v) * w / 4 - 1 / (u + v) ≥ 0 := by
          have h31 : (u + v) * w / 4 - 1 / (u + v) =
              ((u + v) * w * (u + v) - 4) / (4 * (u + v)) := by
            field_simp
            <;> ring
          rw [h31]
          have h32 : 0 < 4 * (u + v) := by positivity
          apply div_nonneg
          have h17 : (u + v) ^ 2 * w ≥ 4 := by
            have h21 : w = 1 / (u * v) := by
              have h14 : u * v ≠ 0 := mul_ne_zero (ne_of_gt hu) (ne_of_gt hv)
              field_simp
              nlinarith [huvw]
            rw [h21] at *
            have h22 : u * v > 0 := mul_pos hu hv
            have : (u + v) ^ 2 ≥ 4 * (u * v) := by
              nlinarith [sq_nonneg (u - v)]
            have h18 : (u + v) ^ 2 / (u * v) ≥ 4 := by
              apply (le_div_iff₀ (by positivity)).mpr
              nlinarith
            have h19 : (u + v) ^ 2 ≥ 4 * (u * v) := by
              nlinarith [sq_nonneg (u - v)]
            have h20 : (u + v) ^ 2 ≥ 4 * (u * v) := h19
            have h23 : (u + v) ^ 2 / (u * v) = (u + v) ^ 2 / (u * v) := by rfl
            have h24 : (u + v) ^ 2 / (u * v) ≥ 4 := h18
            have h25 : (u + v) ^ 2 * (1 / (u * v)) = (u + v) ^ 2 / (u * v) := by
              field_simp
            nlinarith
          linarith
          all_goals positivity
        linarith
      linarith
    linarith

  calc 1 / (a + b) + 1 / (b + c) + 1 / (a + c)
  _ ≤ (a + b) * c / 4 + (b + c) * a / 4 + (c + a) * b / 4 := by
    refine add_le_add (add_le_add ?_ ?_) ?_
    .
      exact h2 ha hb hc habc
    .
      refine h2 hb hc ha ?_
      convert habc using 1
      ring
    .
      rw [add_comm]
      refine h2 hc ha hb ?_
      convert habc using 1
      ring
  _ = (a * b + b * c + c * a) / 2 := by ring
  _ ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    have h : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    linarith