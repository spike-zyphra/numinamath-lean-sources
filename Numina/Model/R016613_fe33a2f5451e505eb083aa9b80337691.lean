import Mathlib

theorem inequalities_189710 (a : ℝ) (ha : a ≠ 2) :
    2 / (a^3 - 8) < 1 / (a^2 - 4 * a + 4) := by
  have h1 : a^2 - 4 * a + 4 = (a - 2) ^ 2 := by 
    ring
  have h2 : a^3 - 8 = (a - 2) * (a ^ 2 + 2 * a + 4) := by 
    ring_nf 
  rw [h1, h2]
  have h3 : a - 2 ≠ 0 := by 
    intro h 
    apply ha 
    linarith 
  have h4 : (a - 2) ^ 2 > 0 := by 
    apply pow_two_pos_of_ne_zero 
    exact h3 
  have h5 : a ^ 2 + 2 * a + 4 > 0 := by 
    nlinarith [sq_nonneg (a + 1)]
  by_cases h6 : a - 2 > 0 
  · -- If a - 2 > 0, then (a - 2) * (a^2 + 2*a + 4) > 0.
    have hx : (a - 2) * (a ^ 2 + 2 * a + 4) > 0 := by 
      nlinarith [h6, h5]
    have h7 : 2 / ((a - 2) * (a ^ 2 + 2 * a + 4)) < 1 / (a - 2) ^ 2 := by 
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_pos_of_ne_zero (show a - 2 ≠ 0 by 
        intro h' 
        apply ha 
        linarith 
      ), sq_nonneg (a - 2), sq_nonneg (a + 2)]
    exact h7 
  · -- If a - 2 ≤ 0.
    have h7 : a - 2 < 0 := by 
      by_contra h 
      push_neg at h 
      have : a - 2 = 0 := by linarith 
      have : a = 2 := by linarith 
      contradiction 
    have hx : (a - 2) * (a ^ 2 + 2 * a + 4) < 0 := by 
      nlinarith [h7, h5]
    have h8 : 2 / ((a - 2) * (a ^ 2 + 2 * a + 4)) < 1 / (a - 2) ^ 2 := by
      have pos1 : (a - 2) * (a ^ 2 + 2 * a + 4) < 0 := hx 
      have pos2 : (a - 2) ^ 2 > 0 := h4 
      have h11 : 2 / ((a - 2) * (a ^ 2 + 2 * a + 4)) - 1 / (a - 2) ^ 2 < 0 := by
        have h12 : 2 / ((a - 2) * (a ^ 2 + 2 * a + 4)) - 1 / (a - 2) ^ 2 =
            (2 * (a - 2) ^ 2 - (a - 2) * (a ^ 2 + 2 * a + 4)) / ((a - 2) * (a ^ 2 + 2 * a + 4) * (a - 2) ^ 2) := by 
          field_simp [(show (a - 2) * (a ^ 2 + 2 * a + 4) ≠ 0 by
            apply mul_ne_zero 
            · -- Show a - 2 ≠ 0 
              intro h'
              apply ha 
              linarith 
            · -- Show a ^ 2 + 2 * a + 4 ≠ 0 
              nlinarith [sq_nonneg (a + 1)]
          ), (show (a - 2) ^ 2 ≠ 0 by
            apply pow_ne_zero 2 
            intro h'
            apply ha 
            linarith 
          )
          ]
          <;> ring 
        rw [h12]
        apply div_neg_of_pos_of_neg 
        · -- Show 2 * (a - 2) ^ 2 - (a - 2) * (a ^ 2 + 2 * a + 4) > 0 
          nlinarith [sq_pos_of_ne_zero (show a - 2 ≠ 0 by
            intro h'
            apply ha 
            linarith 
          ), sq_nonneg (a - 2), sq_nonneg (a + 2)]
        · -- Show (a - 2) * (a ^ 2 + 2 * a + 4) * (a - 2) ^ 2 < 0 
          have pos4 : (a - 2) * (a ^ 2 + 2 * a + 4) < 0 := hx 
          have pos5 : (a - 2) ^ 2 > 0 := h4 
          nlinarith [sq_nonneg (a - 2), sq_nonneg (a ^ 2 + 2 * a + 4), h5, h4]
      linarith
    exact h8