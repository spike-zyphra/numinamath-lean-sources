import Mathlib

open Real Set

theorem algebra_22090 :
    IsLeast {m | ∃a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ m = (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2} (25 / 2) := by
  constructor
  · -- Show that 25/2 is in the set
    use 1 / 2, 1 / 2
    norm_num
  · -- Show that 25/2 is the least value in the set
    intro m hm
    rcases hm with ⟨a, b, ha, hb, h1, h2⟩
    have h3 : b = 1 - a := by linarith
    have ha1 : 0 < 1 - a := by nlinarith
    have h11 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
      rw [show b = 1 - a by linarith]
      have h14 : 0 < a := ha
      have h15 : 0 < 1 - a := by nlinarith
      have h16 : a * (1 - a) ≤ 1 / 4 := by
        nlinarith [sq_nonneg (a - 1 / 2)]
      have h21 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 = a^2 + (1 - a)^2 + 1 / a^2 + 1 / (1 - a)^2 + 4 := by
        field_simp
        nlinarith
      have h26 : a^2 + (1 - a) ^ 2 + 1 / a^2 + 1 / (1 - a)^2 ≥ 17 / 2 := by
        have h23 : 1 / a^2 + 1 / (1 - a) ^ 2 ≥ 8 := by
          have h24 : a * (1 - a) ≤ 1 / 4 := by
            nlinarith [sq_nonneg (a - 1 / 2)]
          have h21 : 1 / a^2 + 1 / (1 - a) ^ 2 - 8 ≥ 0 := by
            have h26 : 0 < a := ha
            have h27 : 0 < 1 - a := by nlinarith
            have h28 : 1 / a ^ 2 + 1 / (1 - a) ^ 2 - 8 = ( (1 - a) ^ 2 + a ^ 2 - 8 * (a ^ 2 * (1 - a) ^ 2 ) ) / ( a ^ 2 * (1 - a) ^ 2 ) := by
              field_simp
              <;> ring
            rw [h28]
            have h29 : ( (1 - a) ^ 2 + a ^ 2 - 8 * (a ^ 2 * (1 - a) ^ 2 ) ) ≥ 0 := by
              nlinarith [sq_nonneg (a ^ 2 - (1 - a) ^ 2), sq_nonneg (a - 1 / 2), sq_nonneg ((a - 1 / 2) * (a + (1 - a) - 1)), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a ^ 2 - (1 / 4)), sq_nonneg ((1 - a) ^ 2 - (1 / 4)), mul_pos ha (show 0 < 1 - a by nlinarith)]
            have h30 : a ^ 2 * (1 - a) ^ 2 > 0 := by positivity
            positivity
          linarith
        have h22 : a^2 + (1 - a) ^ 2 ≥ 1 / 2 := by
          nlinarith [sq_nonneg (a - 1 / 2)]
        have h27 : a^2 + (1 - a) ^ 2 + 1 / a^2 + 1 / (1 - a)^2 ≥ 17 / 2 := by
          nlinarith [h22, h23]
        linarith
      nlinarith [h21, h26]
    nlinarith [h2, h11]