import Mathlib

open Real

theorem algebra_159843 (F : ℝ → ℝ → ℝ)
    (hF : F = fun x y => min (min (2^(-x)) (2^(x - y))) (2^(y - 1))) :
    IsGreatest {z | ∃ x y, z = F x y ∧ 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1} (4 ^ ((1 : ℝ) / 3) / 2) := by
  constructor
  · -- Show that 4^(1/3)/2 is in the set
    use 1 / 3, 2 / 3
    constructor
    · -- Show that 4^(1/3)/2 = F(1/3, 2/3)
      rw [hF]
      have h1 : (2 : ℝ) ^ (- (1 / 3 : ℝ)) = (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
        have h4 : (4 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        rw [h4]
        have h3 : (2 : ℝ) ^ (2 / 3 : ℝ) / 2 = (2 : ℝ) ^ (2 / 3 - 1 : ℝ) := by
          rw [show (2 / 3 - 1 : ℝ) = (2 / 3 : ℝ) - (1 : ℝ) by ring]
          rw [Real.rpow_sub]
          norm_num
          all_goals norm_num
        have h4 : (2 : ℝ) ^ (2 / 3 - 1 : ℝ) = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
          ring_nf
        rw [h3, h4]
      norm_num [h1]
      all_goals norm_num
    all_goals norm_num
  · -- Show that 4^(1/3)/2 is the greatest
    intro z h
    rcases h with ⟨x, y, hz, hx1, hx2, hy1, hy2⟩
    rw [hF] at hz
    by_contra h
    push_neg at h
    have h3 : min (min (2 ^ (-x)) (2 ^ (x - y))) (2 ^ (y - 1)) > (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
      linarith
    have h4 : (2 : ℝ) ^ (-x) ≥ min (min (2 ^ (-x)) (2 ^ (x - y))) (2 ^ (y - 1)) := by
      simp
      all_goals try { linarith }
    have h5 : (2 : ℝ) ^ (x - y) ≥ min (min (2 ^ (-x)) (2 ^ (x - y))) (2 ^ (y - 1)) := by
      simp
      all_goals try { linarith }
    have h6 : (2 : ℝ) ^ (y - 1) ≥ min (min (2 ^ (-x)) (2 ^ (x - y))) (2 ^ (y - 1)) := by
      simp
      all_goals try { linarith }
    have h7 : (2 : ℝ) ^ (-x) > (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
      linarith [h4, h3]
    have h8 : (2 : ℝ) ^ (x - y) > (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
      linarith [h5, h3]
    have h9 : (2 : ℝ) ^ (y - 1) > (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
      linarith [h6, h3]
    have h2 : (4 : ℝ) ^ (1 / 3 : ℝ) / 2 = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
      have h4 : (4 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h4]
      have h3 : (2 : ℝ) ^ (2 / 3 : ℝ) / 2 = (2 : ℝ) ^ (2 / 3 - 1 : ℝ) := by
        rw [show (2 / 3 - 1 : ℝ) = (2 / 3 : ℝ) - (1 : ℝ) by ring]
        rw [Real.rpow_sub]
        norm_num
        all_goals norm_num
      have h4 : (2 : ℝ) ^ (2 / 3 - 1 : ℝ) = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
        ring_nf
      rw [h3, h4]
    -- Contradicts found
    have h10 : x < 1 / 3 := by
      by_contra h
      push_neg at h
      have h11 : -x ≤ - (1 / 3 : ℝ) := by linarith
      have h12 : (2 : ℝ) ^ (-x) ≤ (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals norm_num
        all_goals linarith
      have h13 : (4 : ℝ) ^ (1 / 3 : ℝ) / 2 = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := h2
      have h14 : (2 : ℝ) ^ (-x) ≤ (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
        linarith [h12, h13]
      linarith [h14, h7]
    -- From the second inequality: 2^(x-y) > 4^(1/3)/2 implies x + 1/3 > y
    have h13 : x + 1 / 3 > y := by
      by_contra h
      push_neg at h
      have h14 : x - y ≤ - (1 / 3 : ℝ) := by linarith
      have h15 : (2 : ℝ) ^ (x - y) ≤ (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals norm_num
        all_goals linarith
      have h16 : (4 : ℝ) ^ (1 / 3 : ℝ) / 2 = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := h2
      have h17 : (2 : ℝ) ^ (x - y) ≤ (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
        linarith [h15, h16]
      linarith [h17, h8]
    -- From the third inequality: 2^(y-1) > 4^(1/3)/2 implies y > 2/3
    have h14 : y > 2 / 3 := by
      by_contra h
      push_neg at h
      have h15 : y - 1 ≤ - (1 / 3 : ℝ) := by linarith
      have h16 : (2 : ℝ) ^ (y - 1) ≤ (2 : ℝ) ^ (- (1 / 3 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals norm_num
        all_goals linarith
      have h17 : (4 : ℝ) ^ (1 / 3 : ℝ) / 2 = (2 : ℝ) ^ (- (1 / 3 : ℝ)) := h2
      have h18 : (2 : ℝ) ^ (y - 1) ≤ (4 : ℝ) ^ (1 / 3 : ℝ) / 2 := by
        linarith [h16, h17]
      linarith [h18, h9]
    linarith