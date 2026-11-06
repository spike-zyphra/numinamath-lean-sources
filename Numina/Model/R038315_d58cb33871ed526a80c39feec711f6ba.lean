import Mathlib

open BigOperators Real Set


theorem inequalities_189811 (x : ℝ) (hx : x ≠ 1) :
    abs (-3 / (x - 1)) > abs (- (x - 2) / 2) ↔ -1 < x ∧ x < 4 := by
  constructor
  · -- Assume abs (-3 / (x - 1)) > abs (- (x - 2) / 2), prove -1 < x ∧ x < 4
    intro h
    have h1 : abs (-3 / (x - 1 : ℝ)) = 3 / abs ((x - 1 : ℝ)) := by
      have h2 : abs (-3 / (x - 1 : ℝ)) = abs (-3) / abs ((x - 1 : ℝ)) := by
        field_simp [abs_div]
      have h3 : abs (-3 : ℝ) = (3 : ℝ) := by
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h2, h3]
    have h2 : abs (- (x - 2) / 2 : ℝ) = abs ((x - 2) : ℝ) / 2 := by
      have h3 : abs (- (x - 2) / 2 : ℝ) = abs (- (x - 2)) / abs ((2 : ℝ)) := by
        field_simp [abs_div]
      have h4 : abs (- (x - 2 : ℝ)) = abs ((x - 2 : ℝ)) := by
        rw [abs_neg]
      have h5 : abs ((2 : ℝ)) = (2 : ℝ) := by
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h3, h4, h5]
    rw [h1, h2] at h
    have h3 : abs ((x - 1 : ℝ)) > 0 := by
      have h4 : x - 1 ≠ 0 := by
        intro h5
        apply hx
        linarith
      have h5 : abs ((x - 1 : ℝ)) > 0 := by
        apply abs_pos.mpr
        exact h4
      linarith
    have h4 : 3 * 2 > abs ((x - 2 : ℝ)) * abs ((x - 1 : ℝ)) := by
      have h3_pos : abs ((x - 1 : ℝ)) > 0 := h3
      have h5 : 3 / abs ((x - 1 : ℝ)) > abs ((x - 2) : ℝ) / 2 := by
        linarith [h]
      have h6 : abs ((x - 1 : ℝ)) > 0 := h3
      have h7 : (3 / abs ((x - 1 : ℝ)) ) * (abs ((x - 1 : ℝ)) * 2 ) > (abs ((x - 2) : ℝ) / 2) * (abs ((x - 1 : ℝ)) * 2) := by
        apply mul_lt_mul_of_pos_right
        linarith [h5]
        nlinarith [show abs ((x - 1 : ℝ)) ≥ 0 by apply abs_nonneg, show (2 : ℝ) > 0 by norm_num]
      have h8 : (3 / abs ((x - 1 : ℝ))) * (abs ((x - 1 : ℝ)) * 2) = 3 * 2 := by
        field_simp [show abs ((x - 1 : ℝ)) > 0 by linarith [h3]]
        all_goals nlinarith
      have h9 : (abs ((x - 2) : ℝ) / 2) * (abs ((x - 1 : ℝ)) * 2) = abs ((x - 2) : ℝ) * abs ((x - 1 : ℝ)) := by
        ring_nf
      rw [h8, h9] at h7
      linarith
    have h5 : abs ((x - 2 : ℝ)) * abs ((x - 1 : ℝ)) < (6 : ℝ) := by linarith
    have h8 : -1 < x := by
      by_contra h9
      push_neg at h9
      have h11 : abs ((x - 1 : ℝ)) = 1 - x := by
        rw [abs_of_nonpos]
        nlinarith
        all_goals nlinarith
      have h12 : abs ((x - 2 : ℝ)) = - (x - 2 : ℝ) := by
        rw [abs_of_nonpos]
        nlinarith
        all_goals nlinarith
      rw [h11, h12] at h5
      nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
    have h9 : x < (4 : ℝ) := by
      by_contra h10
      push_neg at h10
      have h11 : abs ((x - 1 : ℝ)) = x - 1 := by
        rw [abs_of_nonneg]
        nlinarith
      have h12 : abs ((x - 2 : ℝ)) = (x - 2 : ℝ) := by
        rw [abs_of_nonneg]
        nlinarith
      rw [h11, h12] at h5
      nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
    constructor
    · linarith
    · linarith
  · -- Assume -1 < x ∧ x < 4 prove abs (-3 / (x - 1)) > abs (- (x - 2) / 2)
    intro h
    rcases h with ⟨h10, h11⟩
    have h1 : abs (-3 / (x - 1 : ℝ)) = 3 / abs ((x - 1 : ℝ)) := by
      have h2 : abs (-3 / (x - 1 : ℝ)) = abs (-3) / abs ((x - 1 : ℝ)) := by
        field_simp [abs_div]
      have h3 : abs (-3 : ℝ) = (3 : ℝ) := by
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h2, h3]
    have h2 : abs (- (x - 2) / 2 : ℝ) = abs ((x - 2) : ℝ) / 2 := by
      have h3 : abs (- (x - 2) / 2 : ℝ) = abs (- (x - 2)) / abs ((2 : ℝ)) := by
        field_simp [abs_div]
      have h4 : abs (- (x - 2 : ℝ)) = abs ((x - 2 : ℝ)) := by
        rw [abs_neg]
      have h5 : abs ((2 : ℝ)) = (2 : ℝ) := by
        norm_num [abs_of_nonneg, abs_of_neg]
      rw [h3, h4, h5]
    rw [h1, h2]
    have h3 : abs ((x - 1 : ℝ)) > 0 := by
      have h4 : x - 1 ≠ 0 := by
        by_contra h5
        have : x = 1 := by linarith
        tauto
      have h5 : abs ((x - 1 : ℝ)) > 0 := by
        apply abs_pos.mpr
        exact h4
      linarith
    have h4 : abs ((x - 2 : ℝ)) * abs ((x - 1 : ℝ)) < (6 : ℝ) := by
      by_cases h20 : x < (1 : ℝ)
      · -- x < 1, so x ∈ (-1, 1)
        have h13 : abs ((x - 1 : ℝ)) = 1 - x := by
          rw [abs_of_nonpos]
          nlinarith
          all_goals nlinarith
        have h14 : abs ((x - 2 : ℝ)) = 2 - x := by
          rw [abs_of_nonpos]
          nlinarith
          all_goals nlinarith
        rw [h13, h14]
        nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
      · -- x ≥ 1, so x ∈ [1, 4)
        have h15 : x ≥ 1 := by linarith
        by_cases h21 : x < (2 : ℝ)
        · -- 1 ≤ x < 2
          have h16 : abs ((x - 1 : ℝ)) = x - 1 := by
            rw [abs_of_nonneg]
            nlinarith
          have h17 : abs ((x - 2 : ℝ)) = 2 - x := by
            rw [abs_of_nonpos]
            nlinarith
            all_goals nlinarith
          rw [h16, h17]
          nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
        · -- x ≥ 2, so x ∈ [2, 4)
          have h18 : x ≥ 2 := by linarith
          have h16 : abs ((x - 1 : ℝ)) = x - 1 := by
            rw [abs_of_nonneg]
            nlinarith
          have h18 : abs ((x - 2 : ℝ)) = x - 2 := by
            rw [abs_of_nonneg]
            nlinarith
          rw [h16, h18]
          nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 1 : ℝ)]
    have h13 : 3 / abs ((x - 1 : ℝ)) > abs ((x - 2 : ℝ)) / 2 := by
      have h3_pos : abs ((x - 1 : ℝ)) > 0 := h3
      have h40 : abs ((x - 2 : ℝ)) * abs ((x - 1 : ℝ)) < (6 : ℝ) := h4
      have h14 : abs ((x - 2 : ℝ)) / 2 < 3 / abs ((x - 1 : ℝ)) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [abs_nonneg ((x - 1 : ℝ)), abs_nonneg ((x - 2 : ℝ)), h40, show abs ((x - 1 : ℝ)) > 0 by linarith [h3]]
      linarith
    linarith