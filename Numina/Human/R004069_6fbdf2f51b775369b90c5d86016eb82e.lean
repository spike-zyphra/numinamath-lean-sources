import Mathlib

open Real

theorem algebra_235968 (a : ℝ) :
  {x : ℝ | x ≠ 0 ∧ abs (x + a) = 1 / x}.encard = 2 ↔
  (a = -2) := by
  have h_card_1 : a > -2 → {x : ℝ | x ≠ 0 ∧ abs (x + a) = 1 / x}.encard = 1 := by
    intro ha
    have : {x | x ≠ 0 ∧ |x + a| = 1 / x} = {-a/2+ sqrt (a^2+4)/2} := by
      ext x
      constructor
      . intro hx
        simp at hx
        simp
        have hx_ne_zero: x ≠ 0 := hx.1
        replace hx : |x + a| = x⁻¹ := hx.2
        field_simp at hx
        by_cases hx1 : x ≥ -a
        . rw [abs_of_nonneg (by linarith)] at hx
          -- have : (x + a / 2) ^ 2 = (a ^ 2 + 4) / 4 := by linarith
          have : (x + a / 2 - √(a ^ 2 + 4) / 2) * (x + a / 2 + √(a ^ 2 + 4) / 2) = 0 := by
            ring_nf
            rw [sq_sqrt (by positivity)]
            linarith

          simp at this
          rcases this with h1 | h2
          . linarith
          . have : √(a ^ 2 + 4) > 0 := by positivity
            nlinarith
        . simp at hx1
          rw [abs_of_neg (by linarith)] at hx
          by_cases ha1 : a < 2
          . -- have : (x + a / 2) ^ 2 = (a ^ 2 - 4) / 4 := by linarith
            have : (x + a / 2) ^ 2 ≥ 0 := by positivity
            -- have : (a ^ 2 - 4) < 0 := by nlinarith
            nlinarith
          . by_cases ha2 : a = 2
            . rw [ha2] at hx
              -- have : (x+1)^2 = 0 := by linarith
              have : x = -1 := by nlinarith
              rw [this, ha2] at hx1
              norm_num at hx1
            . simp at ha1
              have ha3: a > 2 := lt_of_le_of_ne ha1 (Ne.symm ha2)
              have : (x + a / 2 - √(a ^ 2 - 4) / 2) * (x + a / 2 + √(a ^ 2 - 4) / 2) = 0 := by
                ring_nf
                rw [sq_sqrt (by nlinarith)]
                field_simp
                linarith

              simp at this
              rcases this with h1 | h2
              all_goals nlinarith
      . intro hx
        simp at hx
        simp
        have hx_ne_zero: x ≠ 0 := by
          by_contra h_contra
          rw [hx] at h_contra
          have : a ^ 2 + 4 ≥ 0 := by positivity
          have : √(a ^ 2 + 4) = a := by linarith
          rw [sqrt_eq_cases] at this
          rcases this
          all_goals linarith

        suffices |x + a| = x⁻¹ by exact ⟨hx_ne_zero, this⟩
        field_simp
        rw [hx]
        have : -a / 2 + √(a ^ 2 + 4) / 2 + a ≥ 0 := by
          -- have : √(a ^ 2 + 4) > 0 := by positivity
          suffices √(a ^ 2 + 4) ≥ -a by linarith
          have : 2 ≤ √(a ^ 2 + 4) := by
            rw [le_sqrt' (by positivity)]
            have : a ^ 2 ≥ 0 := by positivity
            linarith
          linarith
        rw [abs_of_nonneg this]
        ring_nf
        rw [sq_sqrt (by positivity)]
        field_simp
        ring_nf

    rw [this]
    simp

  have h_card_2 : a = -2 → {x : ℝ | x ≠ 0 ∧ abs (x + a) = 1 / x}.encard = 2 := by
    intro ha
    rw [ha]
    have : {x | x ≠ 0 ∧ |x + -2| = 1 / x} = {1, 1+ sqrt 2}:= by
      ext x
      constructor
      . intro hx
        simp at hx
        have hx_ne_zero: x ≠ 0 := hx.1
        replace hx : |x + -2| = x⁻¹ := hx.2
        field_simp at hx
        by_cases hx1 : x ≥ 2
        . rw [abs_of_nonneg (by linarith)] at hx
          have : (x - 1) ^ 2 = 2 := by linarith
          have : (x - 1- sqrt 2)* (x - 1+ sqrt 2) = 0 := by
            ring_nf
            rw [sq_sqrt (by positivity)]
            linarith
          simp at this
          rcases this with h1 | h2
          . right; simp; linarith
          . have : x = 1 - √2 := by linarith
            rw [this] at hx1
            have : √2 > 0 := by positivity
            linarith

        . simp at hx1
          rw [abs_of_neg (by linarith)] at hx
          ring_nf at hx
          have : (x - 1) ^ 2 = 0:= by linarith
          simp at this
          left; linarith

      . intro hx
        rcases hx with rfl | rfl
        all_goals simp; norm_num
        constructor
        . have : √2 > 0 := by positivity
          linarith
        . field_simp
          have : √2 > 1 := by
            rw [(by norm_num: 1 = √1)]
            apply sqrt_lt_sqrt (by norm_num) (by norm_num)

          rw [abs_of_pos (by linarith)]
          ring_nf
          norm_num

    rw [this]
    rw [Set.encard_pair (by norm_num)]

  have h_card_3 : a < -2 → {x : ℝ | x ≠ 0 ∧ abs (x + a) = 1 / x}.encard = 3 := by
    intro ha
    have : {x | x ≠ 0 ∧ |x + a| = 1 / x} = {-a/2- sqrt (a^2-4)/2, -a/2+ sqrt (a^2-4)/2, -a/2+ sqrt (a^2+4)/2} := by
      ext x
      constructor
      . intro hx
        simp at hx
        have hx_ne_zero: x ≠ 0 := hx.1
        replace hx : |x + a| = x⁻¹ := hx.2
        field_simp at hx
        by_cases hx1 : x ≥ -a
        . rw [abs_of_nonneg (by linarith)] at hx
          have : (x + a / 2) ^ 2 = (a ^ 2 + 4) / 4 := by linarith
          have : (x + a / 2 - √(a ^ 2 + 4) / 2) * (x + a / 2 + √(a ^ 2 + 4) / 2) = 0 := by
            ring_nf
            rw [sq_sqrt (by positivity)]
            linarith

          simp at this
          rcases this with h1 | h2
          . right; right; simp; linarith
          . have : x = -a / 2 - √(a ^ 2 + 4) / 2 := by linarith
            rw [this] at hx1
            have : √(a ^ 2 + 4) ≤ a := by linarith
            rw [sqrt_le_iff] at this
            linarith

        . simp at hx1
          rw [abs_of_neg (by linarith)] at hx
          have : (x + a / 2) ^ 2 = (a ^ 2 - 4) / 4 := by linarith
          have : (x + a / 2 - √(a ^ 2 - 4) / 2) * (x + a / 2 + √(a ^ 2 - 4) / 2) = 0 := by
            ring_nf
            rw [sq_sqrt (by nlinarith)]
            linarith
          simp at this
          rcases this with h1 | h2
          . right; left; linarith
          . left; linarith

      . intro hx
        simp
        have h_ne_zero : x ≠ 0 := by
          by_contra h_contra
          rw [h_contra] at hx
          simp at hx
          rcases hx with h1 | h2 | h3
          . have : √(a ^ 2 - 4) = -a := by linarith
            rw [sqrt_eq_iff_mul_self_eq_of_pos (by linarith)] at this
            linarith
          . -- have : a = √(a ^ 2 - 4) := by linarith
            have : √(a ^ 2 - 4) ≥ 0 := by positivity
            linarith
          . -- have : √(a ^ 2 + 4) = a := by linarith
            have : √(a ^ 2 + 4) ≥ 0 := by positivity
            linarith

        suffices |x + a| = x⁻¹ by exact ⟨h_ne_zero, this⟩
        field_simp
        rcases hx with rfl | rfl | rfl
        . have : -a / 2 - √(a ^ 2 - 4) / 2 + a < 0 := by
            have : √(a ^ 2 - 4) ≥ 0 := by positivity
            linarith

          rw [abs_of_neg this]
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          field_simp

        . have : -a / 2 + √(a ^ 2 - 4) / 2 + a < 0 := by
            suffices √(a ^ 2 - 4) < -a by linarith
            rw [sqrt_lt' (by linarith)]
            linarith

          rw [abs_of_neg this]
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          field_simp

        . have : -a / 2 + √(a ^ 2 + 4) / 2 + a > 0 := by
            suffices -a < √(a ^ 2 + 4) by linarith
            apply lt_sqrt_of_sq_lt
            linarith

          rw [abs_of_pos this]
          ring_nf
          rw [sq_sqrt (by positivity)]
          field_simp
          ring_nf

    rw [this]
    rw [Set.encard_insert_of_not_mem]
    rw [Set.encard_pair]
    norm_num
    . by_contra h_contra
      have : √(a ^ 2 - 4) = √(a ^ 2 + 4) := by linarith
      rw [sqrt_inj (by nlinarith) (by positivity)] at this
      linarith
    . simp
      constructor
      . by_contra h_contra
        have : √(a ^ 2 - 4) = 0 := by linarith
        rw [sqrt_eq_zero (by nlinarith)] at this
        nlinarith
      . by_contra h_contra
        have h_eq: √(a ^ 2 - 4) = -√(a ^ 2 + 4) := by linarith
        have : √(a ^ 2 - 4) ≥ 0 := by positivity
        rw [h_eq] at this
        have : √(a ^ 2 + 4) ≥ 0 := by positivity
        have : √(a ^ 2 + 4) = 0 := by linarith
        rw [sqrt_eq_zero (by nlinarith)] at this
        nlinarith

  constructor
  . by_cases ha1 : a > -2
    . rw [h_card_1 ha1]; simp
    . by_cases ha2 : a = -2
      . rw [h_card_2 ha2]; simp; exact ha2
      . simp at ha1
        have : a < -2 := lt_of_le_of_ne ha1 ha2
        rw [h_card_3 this]; simp
  . exact h_card_2
