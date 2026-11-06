import Mathlib

theorem algebra_160085 (x y : ℤ) :
    x^2 * y + x * y^2 = 2 * x * y + x + y + 1 ↔
    (x, y) = (-1, 0) ∨ (x, y) = (0, -1) ∨ (x, y) = (2, -1) ∨ (x, y) = (-1, 2) := by 
  constructor
  · -- Assume the equation holds, prove the disjunction 
    rintro h_eq
    have h1 : x * y * (x + y - 2) = x + y + 1 := by
      nlinarith 
    have h2 : x + y - 2 ∣ 3 := by 
      have h1' : x + y - 2 ∣ x + y + 1 := by 
        use x * y 
        all_goals linarith 
      have h3 : x + y - 2 ∣ (x + y + 1) - (x + y - 2) := by 
        apply Dvd.dvd.sub h1' 
        exact dvd_refl (x + y - 2)
      have h4 : (x + y + 1) - (x + y - 2) = 3 := by 
        linarith 
      rw [h4] at h3 
      exact h3 
    have h3 : x + y - 2 ∣ 3 := h2
    have h4 : x + y - 2 ≤ 3 := by 
      apply Int.le_of_dvd (by norm_num) h3 
    have h5 : x + y - 2 ≥ -3 := by 
      have h6 : -(x + y - 2) ∣ 3 := by 
        exact Int.neg_dvd.2 h3 
      have h7 : -(x + y - 2) ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      omega 
    interval_cases h9 : x + y - 2 <;> norm_num at h1 <;> 
      norm_num [Prod.ext_iff] at *
      <;> 
        try { 
          omega 
        } 
        <;> 
        try { 
          have : x ≤ 5 := by nlinarith 
          have : x ≥ -5 := by nlinarith 
          have : y ≤ 5 := by nlinarith 
          have : y ≥ -5 := by nlinarith 
          interval_cases x <;> 
            try { 
              omega 
            } 
          <;> 
            try { 
              tauto 
            } 
        }
  · -- Assume the disjunction holds, prove the equation 
    rintro (h | h | h | h)
    · -- Case (-1, 0) 
      simp [Prod.mk.inj_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (0, -1) 
      simp [Prod.mk.inj_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (2, -1) 
      simp [Prod.mk.inj_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (-1, 2) 
      simp [Prod.mk.inj_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num