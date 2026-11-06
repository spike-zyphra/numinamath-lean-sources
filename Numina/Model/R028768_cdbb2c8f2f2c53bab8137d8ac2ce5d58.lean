import Mathlib
theorem algebra_304626 {a b c : ℝ} (h1 : (a + b) * (b + c) * (c + a) = 0) (h2 : a * b * c < 0) :
a / |a| + b / |b| + c / |c| = 1:= by
  have h3 : (a + b) = 0 ∨ (b + c) = 0 ∨ (c + a) = 0 := by
    cases' (mul_eq_zero.mp h1) with h1 h1
    cases' (mul_eq_zero.mp h1) with h1 h1 
    · left; linarith 
    · right; left; linarith 
    · right; right; linarith 
  rcases h3 with h3 | h3 | h3 
  · -- Case where a + b = 0 
    have h4 : b = -a := by 
      linarith 
    rw [show b = -a by linarith [h4]] at h2 
    have h6 : a ≠ 0 := by 
      by_contra h9 
      have h7 : a = 0 := by linarith 
      rw [h7] at h2 
      nlinarith 
    have h7 : c > 0 := by 
      nlinarith [sq_pos_of_ne_zero h6, sq_nonneg a, sq_nonneg c] 
    by_cases h9 : a > 0 
    · -- Case a > 0. 
      have h9a : a > 0 := h9 
      have h10 : b < 0 := by 
        nlinarith 
      have h11 : c > 0 := h7 
      have ha1 : a / |a| = 1 := by 
        rw [abs_of_pos h9a]
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = -1 := by 
        have hb11 : b < 0 := h10 
        rw [abs_of_neg hb11]
        field_simp [show b ≠ 0 by 
          by_contra hb0 
          have : a = 0 := by 
            nlinarith [hb0, show b = -a by linarith [h4]]
          contradiction 
        ] 
      have hc1 : c / |c| = 1 := by 
        rw [abs_of_pos h11 
        ] 
        field_simp [show c ≠ 0 by linarith 
        ] 
      rw [ha1, hb1, hc1 
      ] 
      all_goals norm_num 
    · -- Case a ≤ 0. Then a < 0.
      have h12 : a < 0 := by 
        by_contra h13 
        push_neg at h13 
        have h13' : a = 0 := by 
          linarith 
        rw [h13'] at h2 
        nlinarith 
      have h14 : b > 0 := by 
        nlinarith 
      have h13 : a < 0 := h12 
      have ha1 : a / |a| = -1 := by 
        rw [abs_of_neg h13 
        ] 
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = 1 := by 
        rw [abs_of_pos h14 
        ] 
        field_simp [show b ≠ 0 by 
          by_contra hb0 
          have : a = 0 := by 
            nlinarith [hb0, show b = -a by linarith [h4]
            ] 
          contradiction 
        ] 
      have hc1 : c / |c| = 1 := by 
        rw [abs_of_pos h7 
        ] 
        field_simp 
      rw [ha1, hb1, hc1 
      ] 
      all_goals norm_num 
  · -- Case where b + c = 0
    have h5 : c = -b := by 
      linarith 
    have h6 : c = -b := h5 
    rw [show c = -b by linarith [h5]] at h2 
    have hne0 : b ≠ 0 := by 
      by_contra hb0 
      rw [hb0] at h2 
      nlinarith 
    have h11 : a > 0 := by 
      have hb11 : b ≠ 0 := hne0 
      have hb22 : b ^ 2 > 0 := by 
        exact sq_pos_of_ne_zero hb11 
      nlinarith [sq_nonneg b] 
    by_cases h9 : b > 0 
    · -- Case b > 0. Then c < 0.
      have h10 : c < 0 := by 
        nlinarith [h5, h9] 
      have ha1 : a / |a| = 1 := by 
        rw [abs_of_pos (show a > 0 by linarith 
        )
        ] 
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = 1 := by 
        rw [abs_of_pos h9
        ] 
        field_simp [show b ≠ 0 by linarith 
        ] 
      have hc1 : c / |c| = -1 := by 
        rw [abs_of_neg h10 
        ] 
        field_simp [show c ≠ 0 by linarith 
        ] 
      rw [ha1, hb1, hc1 
      ] 
      all_goals norm_num 
    · -- Case b ≤ 0. Then b < 0.
      have h12 : b < 0 := by 
        by_contra h13 
        push_neg at h13 
        have h14 : b = 0 := by 
          linarith 
        contradiction 
      have h13 : b < 0 := h12 
      have h10 : c > 0 := by 
        nlinarith [h5, h13] 
      have ha1 : a / |a| = 1 := by 
        rw [abs_of_pos (show a > 0 by linarith 
        )
        ] 
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = -1 := by 
        rw [abs_of_neg h13 
        ] 
        field_simp [show b ≠ 0 by linarith 
        ] 
      have hc1 : c / |c| = 1 := by 
        rw [abs_of_pos h10 
        ] 
        field_simp [show c ≠ 0 by linarith 
        ] 
      rw [ha1, hb1, hc1 
      ] 
      all_goals norm_num 
  · -- Case where c + a = 0 
    have h5 : c = -a := by 
      linarith 
    rw [show c = -a by linarith [h5]] at h2 
    have h6 : b > 0 := by 
      have h6a : a ≠ 0 := by 
        by_contra h9 
        have h7 : a = 0 := by linarith 
        rw [h7] at h2 
        nlinarith 
      nlinarith [sq_pos_of_ne_zero h6a, sq_nonneg a, sq_nonneg b]
    by_cases h9 : a > 0 
    · -- Case a > 0. Then c < 0.
      have h10 : c < 0 := by 
        nlinarith [h5, h9] 
      have ha1 : a / |a| = 1 := by 
        rw [abs_of_pos h9
        ] 
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = 1 := by 
        rw [abs_of_pos h6
        ] 
        field_simp [show b ≠ 0 by linarith 
        ] 
      have hc1 : c / |c| = -1 := by 
        rw [abs_of_neg h10 
        ] 
        field_simp [show c ≠ 0 by linarith 
        ] 
      rw [ha1, hb1, hc1
      ] 
      all_goals norm_num 
    · -- Case a ≤ 0. Then a < 0.
      have h12 : a < 0 := by 
        by_contra h13 
        push_neg at h13 
        have h13' : a = 0 := by 
          linarith 
        rw [h13'] at h2 
        nlinarith 
      have h14 : c > 0 := by 
        nlinarith [h5, h12] 
      have ha1 : a / |a| = -1 := by 
        rw [abs_of_neg h12 
        ] 
        field_simp [show a ≠ 0 by linarith 
        ] 
      have hb1 : b / |b| = 1 := by 
        rw [abs_of_pos h6 
        ] 
        field_simp [show b ≠ 0 by linarith 
        ] 
      have hc1 : c / |c| = 1 := by 
        rw [abs_of_pos h14 
        ] 
        field_simp [show c ≠ 0 by linarith 
        ] 
      rw [ha1, hb1, hc1 
      ] 
      all_goals norm_num