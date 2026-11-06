import Mathlib

open Real
open scoped BigOperators

theorem inequalities_3202 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  max (max a b) c < sqrt ((2 * (a^2 + b^2 + c^2)) / 3) := by

  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : max (max a b) c ≥ a := by 
    simp [max_le_iff]
  have h5 : max (max a b) c ≥ b := by 
    simp [max_le_iff]
  have h6 : max (max a b) c ≥ c := by 
    simp [max_le_iff]

  have h7 : (max (max a b) c) ^ 2 < (2 * (a ^ 2 + b ^ 2 + c ^ 2)) / 3 := by
    by_cases h9 : a ≥ b
    · -- if a ≥ b, then max a b = a
      have h10 : max a b = a := by
        apply max_eq_left
        linarith
      by_cases h11 : a ≥ c
      · -- max a b = a, and max a c = a
        have h12 : max (max a b) c = a := by
          rw [h10]
          apply max_eq_left
          linarith
        rw [h12]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
            ]
      · -- max(a, max(b, c)) = max(a, c) = c
        have h13 : max (max a b) c = c := by
          rw [h10]
          have h14 : max a c = c := by
            apply max_eq_right
            linarith
          rw [h14]
        rw [h13]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
            ]
    · -- if a < b, then max a b = b
      have h13 : max a b = b := by
        apply max_eq_right
        linarith
      by_cases h14 : b ≥ c
      · -- max(a, max(b, c)) = max(b, c) = b
        have h15 : max (max a b) c = b := by
          rw [h13]
          have h16 : max b c = b := by
            apply max_eq_left
            linarith
          rw [h16]
        rw [h15]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
            ]
      · -- max(b, c) = c
        have h17 : max (max a b) c = c := by
          rw [h13]
          have h18 : max b c = c := by
            apply max_eq_right
            linarith
          rw [h18]
        rw [h17]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
              mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
              mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
            ]
  
  have h8 : (max (max a b) c) < sqrt ((2 * (a^2 + b^2 + c^2)) / 3) := by
    have h9 : (sqrt ((2 * (a^2 + b^2 + c^2)) / 3)) ^ 2 = (2 * (a^2 + b^2 + c^2)) / 3 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [show (max (max a b) c) ^ 2 < (2 * (a^2 + b^2 + c^2)) / 3 from h7, 
        h9, 
        Real.sqrt_nonneg ((2 * (a^2 + b^2 + c^2)) / 3)
      ]
  exact h8