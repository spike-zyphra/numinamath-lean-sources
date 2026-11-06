import Mathlib

theorem number_theory_254680 (x y : ℕ) (hx : x > 0) (hy : y > 0) :
    x^4 = y^2 + 71 ↔ (x = 6 ∧ y = 35) := by
  constructor
  · -- Assume x^4 = y^2 + 71, prove (x = 6 ∧ y = 35)
    intro h_eq
    -- Show that x ≤ 8
    have h2 : x ≤ 8 := by
      by_contra h2
      push_neg at h2
      have h3 : x ≥ 9 := by omega
      have h4 : x^2 ≥ 81 := by nlinarith [h3]
      have h5 : y < x^2 := by
        nlinarith [sq_nonneg (x^2 : ℕ), sq_nonneg (y : ℕ), h_eq, h4]
      have h6 : x^2 + y ≤ 71 := by
        nlinarith [h_eq, h2, h5]
      have h7 : x^2 ≤ 71 := by
        nlinarith [h6]
      have h8 : x^2 ≥ 81 := by
        nlinarith [h4]
      nlinarith [h7, h8]
    -- Now x ≤ 8, so we can manually check the possible values
    interval_cases x <;> try { 
      { 
        norm_num at h_eq 
        all_goals 
          try { 
            have hy2 : y ≤ 64 := by nlinarith
            interval_cases y <;> omega 
          } 
        <;> try { 
          all_goals 
            try { 
              nlinarith 
            } 
        }
      }
    }
  · -- Backward direction: if (x, y) = (6, 35), then x^4 = y^2 + 71
    rintro ⟨rfl, rfl⟩
    norm_num