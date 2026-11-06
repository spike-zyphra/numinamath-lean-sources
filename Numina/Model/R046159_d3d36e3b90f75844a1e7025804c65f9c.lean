import Mathlib

open BigOperators Real Set

theorem algebra_9240 {a : ℝ} (ha : a ≠ 0) :
    (a ≥ 2 ∧ ∃ x : ℝ, a * sin x - (1/2) * cos (2*x) + a - (3/a) + (1/2) ≤ 0) ↔
    2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Assume (a ≥ 2 ∧ ∃ x : ℝ, a * sin x - (1/2) * cos (2*x) + a - (3/a) + (1/2) ≤ 0), prove (2 ≤ a ∧ a ≤ 3)
    rintro ⟨ha1, ⟨x, hx⟩⟩
    have h1 : 2 ≤ a := by linarith
    have h2 : -1 ≤ sin x ∧ sin x ≤ 1 := by
      constructor
      · exact neg_one_le_sin x
      · exact sin_le_one x
    have h3 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
      rw [cos_two_mul, sin_sq]
      ring_nf
    rw [h3] at hx
    have h4 : sin x ^ 2 + a * sin x + a - 3 / a ≤ 0 := by
      have h5 : a * sin x - (1 / 2) * (1 - 2 * sin x ^ 2) + a - (3 / a) + (1 / 2) ≤ 0 := by
        linarith
      have h7 : a * sin x - (1 / 2) * (1 - 2 * sin x ^ 2) + a - (3 / a) + (1 / 2) = 
          sin x ^ 2 + a * sin x + a - 3 / a := by
        field_simp [ha]
        nlinarith
      rw [h7] at h5
      linarith
    have h6 : a ≤ 3 := by
      by_contra h
      push_neg at h
      have h9 : sin x ^ 2 + a * sin x + a - 3 / a > 0 := by
        have h7 : -1 ≤ sin x ∧ sin x ≤ 1 := by
          constructor
          · exact neg_one_le_sin x
          · exact sin_le_one x
        have h11 : sin x ≤ 1 := by linarith
        have h14 : -1 ≤ sin x := by linarith
        have h12 : sin x ^ 2 + a * sin x + a - 3 / a ≥ 1 - 3 / a := by
          have h116 : -1 ≤ sin x := by linarith
          nlinarith [sq_nonneg (sin x + 1)]
        have h15 : 1 - 3 / a > 0 := by
          have h82 : a > 3 := h
          have h102 : a > 0 := by linarith
          have h92 : (1 * a - 3 : ℝ) / a > 0 := by
            have h71 : (1 * a - 3 : ℝ) > 0 := by
              nlinarith
            have h301 : (a) > 0 := by linarith
            apply div_pos
            all_goals try linarith
          have h33 : (1 - 3 / a : ℝ) = ( (1 * a - 3) / a ) := by
            field_simp [show a ≠ 0 by linarith]
            <;> ring
          nlinarith [h33, h92]
        nlinarith
      linarith
    exact ⟨by linarith, by linarith⟩
  · -- Assume (2 ≤ a ∧ a ≤ 3), prove (a ≥ 2 ∧ ∃ x : ℝ, a * sin x - (1/2) * cos (2*x) + a - (3/a) + (1/2) ≤ 0)
    rintro ⟨ha1, ha2⟩
    constructor
    · exact by linarith
    · -- there exists x
      use Real.pi + Real.pi / 2
      have h9 : sin (Real.pi + Real.pi / 2) = -1 := by
        have h11 : sin (Real.pi + Real.pi / 2) = -1 := by
          have h12 : sin (Real.pi + Real.pi / 2) = -sin (Real.pi / 2) := by
            rw [sin_add, sin_pi, cos_pi]
            ring
          have h13 : sin (Real.pi / 2 : ℝ) = 1 := sin_pi_div_two
          rw [h13] at h12
          linarith
        exact h11
      have h99 : cos (2 * (Real.pi + Real.pi / 2 : ℝ)) = -1 := by
        have h71 : 2 * (Real.pi + Real.pi / 2) = Real.pi + 2 * Real.pi := by ring
        rw [h71]
        have h72 : cos (Real.pi + 2 * Real.pi) = cos Real.pi := by
          rw [cos_add, cos_two_pi, sin_two_pi]
          ring
        have h73 : cos Real.pi = -1 := cos_pi
        linarith
      have h36 : a * sin (Real.pi + Real.pi / 2 : ℝ) - (1/2) * cos (2 * (Real.pi + Real.pi / 2 : ℝ) ) + a - (3/a) + (1/2) ≤ 0 := by
        rw [h9, h99]
        have h41 : a * (-1) - (1/2) * (-1) + a - (3 / a) + (1 / 2) ≤ 0 := by
          have h4000 : a * (-1) - (1 / 2) * (-1) + a - (3 / a) + (1 / 2) = (1 - 3 / a : ℝ) := by
            field_simp [show a ≠ 0 by linarith [ha] ]
            nlinarith
          rw [h4000]
          have h400 : (1 - 3 / a : ℝ) ≤ 0 := by
            have h410 : a > 0 := by
              exact by nlinarith
            have h420 : (1 * a : ℝ) ≤ 3 := by
              have h131 : a ≤ 3 := by linarith
              all_goals nlinarith
            have h430 : (1 * a - 3 : ℝ) ≤ 0 := by
              nlinarith
            have h140 : (1 * a - 3 : ℝ) / a ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              · nlinarith
              · nlinarith
            have h150 : (1 - 3 / a : ℝ) = ( (1 * a - 3) / a ) := by
              field_simp [show a ≠ 0 by linarith]
              <;> ring
            linarith [h150, h140]
          nlinarith
        linarith
      linarith