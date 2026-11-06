import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_163698 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
  logb x y + logb y x ≤ -2 ∨ logb x y + logb y x ≥ 2 := by 
  have h1 : logb x y = log y / log x := by 
    field_simp [logb]
  have h2 : logb y x = log x / log y := by 
    field_simp [logb]

  have h3 : log x ≠ 0 := by
    by_contra h
    have h4 : x = 1 := by
      rw [log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith 
      · linarith 
      · linarith 
    contradiction

  have h4 : log y ≠ 0 := by
    by_contra h
    have h5 : y = 1 := by
      rw [log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith
      · linarith 
      · linarith 
    contradiction

  have h5 : logb x y + logb y x = log y / log x + log x / log y := by 
    rw [h1, h2]

  rw [h5] at *
  by_cases h6 : log y / log x + log x / log y ≥ 2 
  · -- If the expression ≥ 2 then prove the right disjunction
    right 
    linarith 
  · -- Assume the expression < 2, need to prove the left disjunction: expression ≤ -2.
    have h7 : log y / log x + log x / log y ≤ -2 := by 
      have h9 : log y / log x + log x / log y + 2 ≤ 0 := by 
        have h10 : log x ≠ 0 := h3
        have h11 : log y ≠ 0 := h4
        have h12 : log y / log x + log x / log y + 2 = ((log y + log x) ^ 2) / (log x * log y) := by 
          field_simp [h3, h4]
          <;> ring 
        rw [h12]
        by_cases h13 : log x * log y > 0 
        · -- if the denominator is > 0, the expression > 0. We show that this case is impossible.
          have h14 : log y / log x + log x / log y ≥ 2 := by
            have h15 : log x * log y > 0 := h13
            have h16 : log y / log x + log x / log y - 2 ≥ 0 := by 
              have h17 : log y / log x + log x / log y - 2 = (log y - log x) ^ 2 / (log x * log y) := by 
                field_simp [h3, h4]
                <;> ring 
              rw [h17]
              apply div_nonneg 
              · -- Show numerator ≥ 0
                apply sq_nonneg 
              · -- Show denominator ≥ 0 
                linarith 
            linarith 
          linarith 
        · -- The denominator is ≤ 0.
          have h15 : log x * log y ≤ 0 := by
            by_contra h16 
            push_neg at h16 
            have h17 : log y / log x + log x / log y ≥ 2 := by
              have h18 : log x * log y > 0 := by
                nlinarith 
              have h19 : log y / log x + log x / log y - 2 ≥ 0 := by
                have h17 : log y / log x + log x / log y - 2 = (log y - log x) ^ 2 / (log x * log y) := by 
                  field_simp [h3, h4]
                  <;> ring 
                rw [h17]
                apply div_nonneg 
                · -- Show numerator ≥ 0
                  apply sq_nonneg 
                · -- Show denominator ≥ 0 
                  linarith 
              linarith 
            linarith 
          have h10 : ((log y + log x) ^ 2) / (log x * log y) ≤ 0 := by 
            apply div_nonpos_of_nonneg_of_nonpos 
            · -- Show the numerator is non-negative 
              apply pow_two_nonneg 
            · -- Show the denominator is non-positive 
              linarith [h15] 
          linarith 
      linarith 
    left 
    linarith