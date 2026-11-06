import Mathlib

theorem algebra_251162 {x y z : ℤ} (h1 : x * (y + z) = 35) (h2 : y * (z + x) = 32) (h3 : z * (x + y) = 27) :
    (x, y, z) = (5, 4, 3) ∨ (x, y, z) = (-5, -4, -3) := by 

  have h6 : (x = 5 ∧ y = 4 ∧ z = 3) ∨ (x = -5 ∧ y = -4 ∧ z = -3) := by
    have h4a : z * (x - y) = 3 := by 
      nlinarith 
    have h8a : y * (x - z) = 8 := by 
      nlinarith 
    have h10a : x * (y - z) = 5 := by 
      nlinarith 
    have h7a : x ≤ 5 := by 
      have h16 : x * (y - z) = 5 := h10a 
      have h17 : x ∣ 5 := by 
        use y - z 
        all_goals linarith 
      have h18 : x ≤ 5 := by 
        apply Int.le_of_dvd (by norm_num) h17 
      linarith 
    have h8a' : x ≥ -5 := by 
      have h16 : x * (y - z) = 5 := h10a 
      have h17 : x ∣ 5 := by 
        use y - z 
        all_goals linarith 
      have h18 : x ≥ -5 := by 
        have h19 : -x ∣ 5 := by 
          exact Int.neg_dvd.2 h17 
        have h20 : -x ≤ 5 := by 
          apply Int.le_of_dvd (by norm_num) h19 
        omega 
      linarith 
    have h12b : y ≤ 8 := by 
      have h16b : y * (x - z) = 8 := h8a 
      have h17b : y ∣ 8 := by 
        use x - z 
        all_goals linarith 
      have h18b : y ≤ 8 := by 
        apply Int.le_of_dvd (by norm_num) h17b 
      linarith 
    have h13b : y ≥ -8 := by 
      have h16b : y * (x - z) = 8 := h8a 
      have h17b : y ∣ 8 := by 
        use x - z 
        all_goals linarith 
      have h18b : y ≥ -8 := by 
        have h24b : -y ∣ 8 := by 
          exact Int.neg_dvd.2 h17b 
        have h25b : -y ≤ 8 := by 
          apply Int.le_of_dvd (by norm_num) h24b 
        omega 
      linarith 
    have h11b : z ≤ 3 := by 
      have h16b : z * (x - y) = 3 := h4a 
      have h17b : z ∣ 3 := by 
        use x - y 
        all_goals linarith 
      have h18b : z ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h17b 
      linarith 
    have h14b : z ≥ -3 := by 
      have h16b : z * (x - y) = 3 := h4a 
      have h17b : z ∣ 3 := by 
        use x - y 
        all_goals linarith 
      have h18b : z ≥ -3 := by 
        have h24b : -z ∣ 3 := by 
          exact Int.neg_dvd.2 h17b 
        have h25b : -z ≤ 3 := by 
          apply Int.le_of_dvd (by norm_num) h24b 
        omega 
      linarith 
    interval_cases x <;> try { 
      omega 
    } <;> try { 
      interval_cases y <;> 
      try { 
        omega 
      } <;> try { 
          interval_cases z <;> 
          try { 
            norm_num at h4a h8a h10a ⊢ 
          }
        }
    }
  rcases h6 with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · -- First case
    simp [hx, hy, hz, Prod.ext_iff] 
  · -- Second case 
    simp [hx, hy, hz, Prod.ext_iff]