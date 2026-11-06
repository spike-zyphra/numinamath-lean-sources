import Mathlib

open Real

theorem algebra_160248 : cos (20 * π / 180) * cos (40 * π / 180) * cos (60 * π / 180) * cos (80 * π / 180) = 0.0625 := by
  have h1 : cos (60 * π / 180) = 1 / 2 := by
    have h2 : 60 * π / 180 = π / 3 := by
      ring
    rw [h2]
    exact Real.cos_pi_div_three
  have h2 : cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = 1 / 8 := by
    have h3 : cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = sin (160 * π / 180) / (8 * sin (20 * π / 180)) := by
      have eq4 : cos (20 * π / 180) = sin (40 * π / 180) / (2 * sin (20 * π / 180)) := by
        have eq5 : sin (40 * π / 180) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
          have h8 : sin (2 * (20 * π / 180)) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
            rw [sin_two_mul]
          have : 2 * (20 * π / 180) = 40 * π / 180 := by ring
          rw [this] at h8
          linarith
        have h3' : sin (20 * π / 180) ≠ 0 := by
          have h3' : sin (20 * π / 180) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          linarith
        field_simp [h3']
        nlinarith
      have eq5 : cos (40 * π / 180) = sin (80 * π / 180) / (2 * sin (40 * π / 180)) := by
        have eq6 : sin (80 * π / 180) = 2 * sin (40 * π / 180) * cos (40 * π / 180) := by
          have h8 : sin (2 * (40 * π / 180)) = 2 * sin (40 * π / 180) * cos (40 * π / 180) := by
            rw [sin_two_mul]
          have : 2 * (40 * π / 180) = 80 * π / 180 := by ring
          rw [this] at h8
          linarith
        have h3' : sin (40 * π / 180) ≠ 0 := by
          have h3' : sin (40 * π / 180) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          linarith
        field_simp [h3']
        nlinarith
      have eq6 : cos (80 * π / 180) = sin (160 * π / 180) / (2 * sin (80 * π / 180)) := by
        have eq7 : sin (160 * π / 180) = 2 * sin (80 * π / 180) * cos (80 * π / 180) := by
          have h8 : sin (2 * (80 * π / 180)) = 2 * sin (80 * π / 180) * cos (80 * π / 180) := by
            rw [sin_two_mul]
          have : 2 * (80 * π / 180) = 160 * π / 180 := by ring
          rw [this] at h8
          linarith
        have h3' : sin (80 * π / 180) ≠ 0 := by
          have h3' : sin (80 * π / 180) > 0 := by
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          linarith
        field_simp [h3']
        nlinarith
      calc
        cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180)
          = (sin (40 * π / 180) / (2 * sin (20 * π / 180))) * (sin (80 * π / 180) / (2 * sin (40 * π / 180))) * (sin (160 * π / 180) / (2 * sin (80 * π / 180)) ) := by
            rw [eq4, eq5, eq6]
        _ = sin (160 * π / 180) / (8 * sin (20 * π / 180)) := by
          field_simp [(show sin (20 * π / 180) ≠ 0 by
            apply ne_of_gt
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          ), (show sin (40 * π / 180) ≠ 0 by
            apply ne_of_gt
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          ), (show sin (80 * π / 180) ≠ 0 by
            apply ne_of_gt
            apply sin_pos_of_pos_of_lt_pi
            all_goals
              linarith [Real.pi_pos]
          )
          ]
          <;> ring
    rw [h3]
    have eq8 : sin (160 * π / 180) = sin (20 * π / 180) := by
      have h13 : 160 * π / 180 = Real.pi - (20 * π / 180) := by ring
      rw [h13]
      rw [sin_pi_sub]
    rw [eq8]
    have h3' : sin (20 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals
        linarith [Real.pi_pos]
    have h42 : sin (20 * π / 180) ≠ 0 := by linarith [h3']
    field_simp [h42]
    all_goals
      linarith
  calc
    cos (20 * π / 180) * cos (40 * π / 180) * cos (60 * π / 180) * cos (80 * π / 180)
      = (cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180)) * (cos (60 * π / 180)) := by ring
    _ = (1 / 8) * (1 / 2) := by
      rw [h2, h1]
    _ = (1 / 16 : ℝ) := by norm_num
    _ = 0.0625 := by norm_num