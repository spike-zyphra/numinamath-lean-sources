import Mathlib
open Real

theorem algebra_97605 :
IsLeast {z : ℝ | 0 < z ∧ ∃ x : ℝ, cos x = 0 ∧ cos (x + z) = 1 / 2} (π / 6) := by
  constructor 
  · -- Show π/6 is in the set
    constructor 
    · -- π is positive, so π/6 is positive 
      linarith [Real.pi_pos] 
    · -- Use x = 3 * π / 2
      use (3 * π / 2)
      constructor
      · -- Show cos(3 * π / 2) = 0 
        have h1 : cos (3 * π / 2) = 0 := by
          have h2 : cos (3 * π / 2) = cos (π + π / 2) := by 
            ring_nf 
          rw [h2]
          have h3 : cos (π + π / 2) = -cos (π / 2) := by 
            rw [cos_add]
            simp [cos_pi, sin_pi]
          have h4 : cos (π / 2) = 0 := by 
            exact cos_pi_div_two 
          rw [h3, h4]
          all_goals norm_num 
        linarith 
      · -- Show cos(3 * π / 2 + π / 6) = 1 / 2 
        have h2 : cos (3 * π / 2 + π / 6) = 1 / 2 := by 
          have h3 : cos (3 * π / 2 + π / 6) = cos (3 * π / 2) * cos (π / 6) - sin (3 * π / 2) * sin (π / 6) := by 
            rw [cos_add]
          have h4 : cos (3 * π / 2) = 0 := by 
            have h2 : cos (3 * π / 2) = cos (π + π / 2) := by
              ring_nf 
            rw [h2]
            have h3 : cos (π + π / 2) = -cos (π / 2) := by 
              rw [cos_add]
              simp [cos_pi, sin_pi]
            have h4 : cos (π / 2) = 0 := by
              exact cos_pi_div_two
            rw [h3, h4]
            all_goals norm_num 
          have h5 : sin (3 * π / 2) = -1 := by 
            have h6 : sin (3 * π / 2) = sin (π + π / 2) := by 
              ring_nf
            rw [h6]
            have h7 : sin (π + π / 2) = -sin (π / 2) := by 
              rw [sin_add]
              simp [cos_pi, sin_pi]
            have h8 : sin (π / 2) = 1 := by 
              exact sin_pi_div_two 
            rw [h7, h8]
            all_goals norm_num 
          have h6 : cos (π / 6) = Real.sqrt 3 / 2 := by 
            exact cos_pi_div_six 
          have h7 : sin (π / 6) = 1 / 2 := by 
            exact sin_pi_div_six 
          rw [h3, h4, h5, h6, h7]
          all_goals linarith 
        linarith
  · -- Show that π/6 is the smallest
    intro z ⟨hz, x, hx, h⟩
    by_contra h1 
    push_neg at h1 
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq x
    rw [show cos x = 0 by linarith [hx]] at h2 
    have h3 : sin x ^ 2 = 1 := by 
      nlinarith 
    have h4 : sin x = 1 ∨ sin x = -1 := by
      have h5 : sin x ^ 2 = 1 := h3
      rw [sq_eq_one_iff] at h5
      all_goals tauto 
    have h5 : cos (x + z) = cos x * cos z - sin x * sin z := by 
      rw [cos_add]
    rw [show cos x = 0 by linarith [hx]] at h5 
    have h6 : - sin x * sin z = 1 / 2 := by 
      linarith [h, h5]
    rcases h4 with h4 | h4 
    · -- sin x = 1 
      have h7 : sin z = -1 / 2 := by 
        rw [h4] at h6 
        nlinarith 
      have h8 : sin z > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        all_goals 
          linarith [Real.pi_gt_three, h1]
      nlinarith [h7, h8]
    · -- sin x = -1 
      have h7 : sin z = 1 / 2 := by 
        rw [h4] at h6 
        nlinarith 
      have h8 : z < π / 6 := by 
        linarith 
      have h9 : sin z < sin (π / 6) := by 
        apply sin_lt_sin_of_lt_of_le_pi_div_two 
        all_goals 
          linarith [Real.pi_pos, h1]
      have h10 : sin (π / 6) = 1 / 2 := sin_pi_div_six 
      nlinarith [h7, h9, h10]