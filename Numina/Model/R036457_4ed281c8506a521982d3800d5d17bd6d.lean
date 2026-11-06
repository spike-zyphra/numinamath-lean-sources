import Mathlib

theorem algebra_319047 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = 0) :
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = 0 := by

  have ha1 : a / abs a = if a > 0 then 1 else -1 := by 
    split_ifs with h2
    · -- if a > 0
      rw [abs_of_pos h2]
      field_simp
    · -- if a ≤ 0
      have h3 : a < 0 := by 
        by_contra h4
        push_neg at h4
        have h4' : a = 0 := by linarith
        contradiction
      rw [abs_of_neg h3]
      field_simp
  have h2 : b / abs b = if b > 0 then 1 else -1 := by 
    split_ifs with h3
    · -- if b > 0
      rw [abs_of_pos h3]
      field_simp
    · -- if b ≤ 0
      have h4 : b < 0 := by 
        by_contra h5
        push_neg at h5
        have h5' : b = 0 := by linarith
        contradiction
      rw [abs_of_neg h4]
      field_simp
  have h3 : c / abs c = if c > 0 then 1 else -1 := by 
    split_ifs with h4
    · -- if c > 0
      rw [abs_of_pos h4]
      field_simp
    · -- if c ≤ 0
      have h5 : c < 0 := by 
        by_contra h6
        push_neg at h6
        have h6' : c = 0 := by linarith
        contradiction
      rw [abs_of_neg h5]
      field_simp

  have h4 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    have h5 : abs (a * b * c) = abs a * abs b * abs c := by
      simp [abs_mul]
    rw [h5]
    <;> field_simp [ha, hb, hc] <;> ring

  rw [h4, ha1, h2, h3]

  by_cases h5 : a > 0
  · -- Case a > 0
    rw [if_pos h5]
    by_cases h6 : b > 0
    · -- Case b > 0
      rw [if_pos h6]
      have hc4 : c < 0 := by
        nlinarith
      rw [if_neg (show ¬(c > 0) by linarith)]
      norm_num [hc4]
    · -- Case b ≤ 0
      rw [if_neg (show ¬(b > 0) by 
        by_contra h
        linarith
      )
      ]
      have hb4 : b < 0 := by 
        by_contra h4
        push_neg at h4
        have h4' : b = 0 := by linarith
        contradiction
      by_cases hc2 : c > 0
      · -- Case c > 0
        rw [if_pos hc2]
        norm_num [hb4, hc2]
      · -- Case c ≤ 0
        rw [if_neg (show ¬(c > 0) by 
          by_contra h
          linarith
        )
        ]
        have hc4 : c < 0 := by
          by_contra h4
          push_neg at h4
          have h4' : c = 0 := by linarith
          contradiction
        norm_num [hb4, hc4]
  · -- Case a ≤ 0
    rw [if_neg (show ¬(a > 0) by 
      by_contra h
      linarith
    )
    ]
    have ha4 : a < 0 := by 
      by_contra h4
      push_neg at h4
      have h4' : a = 0 := by linarith
      contradiction
    by_cases h6 : b > 0
    · -- Case b > 0
      rw [if_pos h6]
      by_cases hc2 : c > 0
      · -- Case c > 0
        rw [if_pos hc2]
        norm_num [ha4, hc2]
      · -- Case c ≤ 0
        rw [if_neg (show ¬(c > 0) by 
          by_contra h
          linarith
        )
        ]
        have hc4 : c < 0 := by
          by_contra h4
          push_neg at h4
          have h4' : c = 0 := by linarith
          contradiction
        norm_num [ha4, hc4]
    · -- Case b ≤ 0
      rw [if_neg (show ¬(b > 0) by 
        by_contra h
        linarith
      )
      ]
      have hb4 : b < 0 := by 
        by_contra h4
        push_neg at h4
        have h4' : b = 0 := by linarith
        contradiction
      have hc5 : c > 0 := by
        nlinarith
      rw [if_pos hc5]
      norm_num [ha4, hb4, hc5]