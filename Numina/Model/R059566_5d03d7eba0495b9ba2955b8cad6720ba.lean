import Mathlib

theorem algebra_4566 :
    IsGreatest {z : ℤ | ∃ x y, z = x + y ∧ x * y - x + y = 6} 6 := by
  constructor
  · -- Show that 6 is in the set
    use 0, 6
    all_goals norm_num 
  · -- Show that any z in the set is at most 6 
    intro z h
    rcases h with ⟨x, y, h_eq, heq⟩ 
    have h : x + y ≤ 6 := by 
      have eq1 : (x + 1) * (y - 1) = 5 := by
        nlinarith 
      have h1 : (x + 1) ∣ 5 := by
        use (y - 1)
        linarith [eq1] 
      have h2 : (x + 1) = 1 ∨ (x + 1) = 5 ∨ (x + 1) = -1 ∨ (x + 1) = -5 := by 
        have h3 : (x + 1) ∣ 5 := h1
        have h4 : (x + 1) = 1 ∨ (x + 1) = 5 ∨ (x + 1) = -1 ∨ (x + 1) = -5 := by 
          have h5 : (x + 1) ≤ 5 := by
            apply Int.le_of_dvd (by norm_num) h3 
          have h6 : (x + 1) ≥ -5 := by 
            have h7 : -(x + 1) ∣ 5 := by
              exact Int.neg_dvd.2 h3 
            have h8 : -(x + 1) ≤ 5 := by 
              apply Int.le_of_dvd (by norm_num) h7 
            linarith [h8] 
          interval_cases (x + 1) <;> try { tauto } 
          <;> try { contradiction } <;> omega 
        assumption 
      rcases h2 with h2 | h2 | h2 | h2 
      · -- Case where $x + 1 = 1$, so $x = 0$, and $y - 1 = 5$, so $y = 6$
        have hx : x = 0 := by 
          linarith 
        have hy : y = 6 := by 
          have : (y - 1) = 5 := by
            nlinarith [h2, eq1] 
          linarith 
        linarith [hx, hy] 
      · -- Case where $x + 1 = 5$, so $x = 4$, and $y - 1 = 1$, so $y = 2$
        have hx : x = 4 := by 
          linarith 
        have hy : y = 2 := by 
          have : (y - 1) = 1 := by
            nlinarith [h2, eq1] 
          linarith 
        linarith [hx, hy] 
      · -- Case where $x + 1 = -1$, so $x = -2$, and $y - 1 = -5$, so $y = -4$
        have hx : x = -2 := by 
          linarith 
        have hy : y = -4 := by 
          have : (y - 1) = -5 := by
            nlinarith [h2, eq1] 
          linarith 
        linarith [hx, hy] 
      · -- Case where $x + 1 = -5$, so $x = -6$, and $y - 1 = -1$, so $y = 0$
        have hx : x = -6 := by 
          linarith 
        have hy : y = 0 := by 
          have : (y - 1) = -1 := by
            nlinarith [h2, eq1] 
          linarith 
        linarith [hx, hy] 
    linarith [h_eq, h]