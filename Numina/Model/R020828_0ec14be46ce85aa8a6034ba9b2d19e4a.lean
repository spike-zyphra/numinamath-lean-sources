import Mathlib

theorem algebra_93182 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = 0) :
    a / abs a + b / abs b + c / abs c + (a * b * c) / abs (a * b * c) = 0 := by
  have h1 : a / abs a = if a > 0 then 1 else -1 := by
    split_ifs with ha1
    · -- If a > 0 then a / abs a = 1
      rw [abs_of_pos ha1]
      field_simp [ha]
    · -- If a ≤ 0 then a > 0 is false, and so a < 0 (since a ≠ 0 by ha)
      have ha2 : a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        contradiction
      rw [abs_of_neg ha2]
      field_simp [ha]

  have h2 : b / abs b = if b > 0 then 1 else -1 := by
    split_ifs with hb1
    · -- If b > 0 then a / abs a = 1
      rw [abs_of_pos hb1]
      field_simp [hb]
    · -- If b ≤ 0 then b > 0 is false, and so b < 0 (since b ≠ 0 by hb)
      have hb2 : b < 0 := by
        by_contra h
        push_neg at h
        have : b = 0 := by linarith
        contradiction
      rw [abs_of_neg hb2]
      field_simp [hb]

  have h3 : c / abs c = if c > 0 then 1 else -1 := by
    split_ifs with hc1
    · -- If c > 0 then c / abs c = 1
      rw [abs_of_pos hc1]
      field_simp [hc]
    · -- If c ≤ 0 then c > 0 is false, and so c < 0 (since c ≠ 0 by hc)
      have hc2 : c < 0 := by
        by_contra h
        push_neg at h
        have : c = 0 := by linarith
        contradiction
      rw [abs_of_neg hc2]
      field_simp [hc]

  have h4 : (a * b * c) / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    have h2 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    field_simp [abs_mul, abs_mul, h2]
    <;> ring_nf
    <;> simp [abs_mul]

  rw [h4, h1, h2, h3]

  by_cases ha_pos : a > 0
  · -- Case where a > 0
    simp [ha_pos]
    by_cases hb_pos : b > 0
    · -- Case where a > 0 and b > 0
      simp [hb_pos]
      by_cases hc_pos : c > 0
      · -- Case where a > 0, b > 0, and c > 0
        exfalso
        have h1 : a + b + c > 0 := by
          nlinarith
        nlinarith
      · -- Case where a > 0, b > 0, and c ≤ 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : c = 0 := by nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
    · -- Case where a > 0 and b ≤ 0
      simp [hb_pos]
      by_cases hc_pos : c > 0
      · -- Case where a > 0, b ≤ 0, c > 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : b = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
      · -- Case where a > 0, b ≤ 0, c ≤ 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : b = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          exfalso
          have h_zero : c = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
  · -- Case where a ≤ 0
    simp [ha_pos]
    by_cases hb_pos : b > 0
    · -- Case where b > 0
      simp [hb_pos]
      by_cases hc_pos : c > 0
      · -- Case where a ≤ 0, b > 0, c > 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : a = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
      · -- Case where a ≤ 0, b > 0, c ≤ 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : a = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          exfalso
          have h_zero : c = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
    · -- Case where b ≤ 0
      simp [hb_pos]
      by_cases hc_pos : c > 0
      · -- Case where a ≤ 0, b ≤ 0, c > 0
        simp [hc_pos]
        all_goals try { nlinarith }
        all_goals try { 
          exfalso
          have h_zero : a = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          exfalso
          have h_zero : b = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }
      · -- Case where a ≤ 0, b ≤ 0, c ≤ 0
        simp [hc_pos]
        all_goals try { 
          exfalso
          have h_zero : a = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          exfalso
          have h_zero : b = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          exfalso
          have h_zero : c = 0 := by
            nlinarith
          contradiction
        }
        all_goals try { 
          nlinarith
        }