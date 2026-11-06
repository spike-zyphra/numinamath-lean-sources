import Mathlib

open Real Set
open scoped Real

theorem algebra_3737 (y : ℝ → ℝ)
  (hy : y = λ x => 4 * sin (x * π / 180) * cos (x * π / 180) - 2 * cos (x * π / 180) - 2 * sin (x * π / 180) + 1)
  (x : ℝ) (hx : x ∈ Icc 0 90) :
  y x > 0 ↔ 30 < x ∧ x < 60 := by
  rcases hx with ⟨hx0, hx90⟩
  have h1 : 0 ≤ x := hx0
  have h2 : x ≤ 90 := hx90
  have h3 : y x = 4 * sin (x * π / 180) * cos (x * π / 180) - 2 * cos (x * π / 180) - 2 * sin (x * π / 180) + 1 := by 
    rw [hy]
  have h4 : y x = (2 * sin (x * π / 180) - 1) * (2 * cos (x * π / 180) - 1) := by
    rw [h3]
    ring 
  constructor
  · -- Forward
    intro h
    have h5 : (2 * sin (x * π / 180) - 1) * (2 * cos (x * π / 180) - 1) > 0 := by
      rw [h4] at h 
      linarith
    have h6 : (2 * sin (x * π / 180) - 1 > 0 ∧ 2 * cos (x * π / 180) - 1 > 0) ∨ (2 * sin (x * π / 180) - 1 < 0 ∧ 2 * cos (x * π / 180) - 1 < 0) := by
      apply mul_pos_iff.mp 
      linarith
    rcases h6 with (h7 | h8)
    · -- Case where both factors are positive
      have h71 : 2 * sin (x * π / 180) - 1 > 0 := h7.1
      have h72 : 2 * cos (x * π / 180) - 1 > 0 := h7.2 
      have h73 : sin (x * π / 180) > 1 / 2 := by linarith
      have h74 : cos (x * π / 180) > 1 / 2 := by linarith
      have h8 : x * π / 180 > Real.pi / 6 := by 
        by_contra h 
        push_neg at h 
        -- In this case, angle x * π / 180 ≤ π / 6
        have h9 : sin (x * π / 180) ≤ 1 / 2 := by 
          have h10 : sin (x * π / 180) ≤ sin (Real.pi / 6) := by 
            apply sin_le_sin_of_le_of_le_pi_div_two 
            all_goals 
              nlinarith [Real.pi_pos]
          have h11 : sin (Real.pi / 6) = 1 / 2 := by 
            exact sin_pi_div_six
          nlinarith [h11, h10]
        linarith 
      have h9 : x > 30 := by 
        by_contra h
        push_neg at h
        -- If x < 30, then angle x * π / 180 < π / 6
        nlinarith [Real.pi_pos]
      have h10 : x * π / 180 < Real.pi / 3 := by 
        by_contra h
        push_neg at h 
        -- In this case, angle x * π / 180 ≥ π / 3
        have h11 : cos (x * π / 180) ≤ 1 / 2 := by 
          have h12 : cos (x * π / 180) ≤ cos (Real.pi / 3) := by 
            apply cos_le_cos_of_nonneg_of_le_pi 
            all_goals 
              nlinarith [Real.pi_pos]
          have h13 : cos (Real.pi / 3) = 1 / 2 := by 
            exact cos_pi_div_three
          nlinarith [h13, h12]
        linarith 
      have h11 : x < 60 := by 
        by_contra h 
        push_neg at h 
        -- If x ≥ 60, then angle x * π / 180 ≥ π / 3
        nlinarith [Real.pi_pos]
      constructor <;> linarith 
    · -- Case where both factors are negative 
      exfalso 
      have h81 : 2 * sin (x * π / 180) - 1 < 0 := h8.1
      have h82 : 2 * cos (x * π / 180) - 1 < 0 := h8.2 
      have h5 : sin (x * π / 180) < 1 / 2 := by linarith 
      have h5 : cos (x * π / 180) < 1 / 2 := by linarith 
      have h85 : x * π / 180 < Real.pi / 6 := by 
        by_contra h 
        push_neg at h 
        have h9 : sin (x * π / 180) ≥ 1 / 2 := by 
          have h10 : sin (x * π / 180) ≥ sin (Real.pi / 6) := by 
            apply sin_le_sin_of_le_of_le_pi_div_two 
            all_goals 
              nlinarith [Real.pi_pos]
          have h11 : sin (Real.pi / 6) = 1 / 2 := by 
            exact sin_pi_div_six 
          nlinarith [h11, h10]
        linarith 
      have h88 : x * π / 180 > Real.pi / 3 := by 
        by_contra h 
        push_neg at h 
        have h89 : cos (x * π / 180) ≥ 1 / 2 := by 
          have h90 : cos (x * π / 180) ≥ cos (Real.pi / 3) := by 
            apply cos_le_cos_of_nonneg_of_le_pi 
            all_goals 
              nlinarith [Real.pi_pos]
          have h91 : cos (Real.pi / 3) = 1 / 2 := by 
            exact cos_pi_div_three 
          nlinarith [h91, h90]
        linarith 
      -- These bounds are contradictory
      nlinarith [Real.pi_pos]
  · -- Backward 
    rintro ⟨h1, h2⟩ 
    have h3 : 0 ≤ x := by linarith 
    have h4 : x ≤ 90 := by linarith 
    have eq1 : y x = (2 * sin (x * π / 180) - 1) * (2 * cos (x * π / 180) - 1) := by 
      rw [show y x = 4 * sin (x * π / 180) * cos (x * π / 180) - 2 * cos (x * π / 180) - 2 * sin (x * π / 180) + 1 by rw [hy]]
      ring
    have h5 : sin (x * π / 180) > 1 / 2 := by 
      have h6 : x * π / 180 > Real.pi / 6 := by 
        nlinarith [Real.pi_pos] 
      have h7 : sin (x * π / 180) > sin (Real.pi / 6) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two 
        all_goals 
          nlinarith [Real.pi_pos] 
      have h8 : sin (Real.pi / 6) = 1 / 2 := by 
        exact sin_pi_div_six 
      nlinarith [h8, h7] 
    have h9 : cos (x * π / 180) > 1 / 2 := by 
      have h10 : x * π / 180 < Real.pi / 3 := by
        nlinarith [Real.pi_pos] 
      have h11 : cos (x * π / 180) > cos (Real.pi / 3) := by 
        apply cos_lt_cos_of_nonneg_of_le_pi 
        all_goals 
          nlinarith [Real.pi_pos] 
      have h12 : cos (Real.pi / 3) = 1 / 2 := by 
        exact cos_pi_div_three 
      nlinarith [h12, h11] 
    have h13 : 2 * sin (x * π / 180) - 1 > 0 := by
      linarith 
    have h14 : 2 * cos (x * π / 180) - 1 > 0 := by
      linarith 
    have h15 : y x > 0 := by
      rw [eq1] 
      nlinarith 
    linarith