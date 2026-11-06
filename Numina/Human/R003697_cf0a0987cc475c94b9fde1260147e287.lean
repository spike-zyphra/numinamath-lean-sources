import Mathlib
theorem algebra_208522
  (a : ℝ) (f : ℝ → ℝ)
  (hf : f = fun x => abs (x + 1) + abs (a * x + 1)) :
  IsLeast {x | ∃ y, f y = x} (3 / 2) ↔ a = -1/2 ∨ a = -2 := by

  unfold IsLeast lowerBounds
  constructor
  . intro ⟨ ⟨ y, hy ⟩, hx ⟩
    simp at hx
    rw [hf] at hx hy
    simp at hx hy

    by_cases ha0 : a = 0
    . subst a
      have := hx (-1)
      ring_nf at this
      norm_num at this

    . have hx1 := hx (-1/a)
      field_simp at hx1
      have hx2 := hx (-1)
      ring_nf at hx2
      norm_num at hx2

      rcases lt_trichotomy a 1 with (ha2 | rfl | ha1)
      . rcases lt_trichotomy a (-2) with (ha3 | rfl | ha4)
        . rw [abs_div] at hx1
          repeat rw [abs_of_neg (by linarith)] at hx1
          ring_nf at hx1
          rw [(by field_simp: a * a⁻¹ = 1)] at hx1
          have : 2*a⁻¹ ≤ -1  := by linarith
          rw [← mul_le_mul_left_of_neg (by linarith: a<0)] at this
          field_simp at this
          linarith

        . right; rfl
        . rcases lt_trichotomy a (-1/2) with (ha6 | rfl | ha5)
          . rcases lt_trichotomy y (-1/a) with (hy2 | rfl | hy1)
            . rcases lt_trichotomy y (-1) with (hy3 | rfl | hy4)
              . rw [abs_of_neg (by linarith)] at hy
                have : a * y + 1 > 0 := by
                  rw [← mul_lt_mul_left_of_neg (by linarith: a<0)] at hy2
                  field_simp at hy2
                  linarith
                rw [abs_of_pos this] at hy
                have : (a-1) * y = 3/2 := by linarith
                have : a-1 ≠ 0 := by linarith
                have : y = 3/2 / (a-1) := by
                  field_simp
                  linarith
                rw [this] at hy3
                rw [← mul_lt_mul_left_of_neg (by linarith: 2 * (a - 1)<0)] at hy3

                field_simp at hy3

                linarith

              . ring_nf at hy
                norm_num at hy
                rw [abs_eq (by norm_num)] at hy
                rcases hy with (hy | hy)
                . left; linarith
                . left; linarith

              . rw [abs_of_pos (by linarith)] at hy

                have : a * y + 1 > 0 := by
                  rw [← mul_lt_mul_left_of_neg (by linarith: a<0)] at hy2
                  field_simp at hy2
                  linarith
                rw [abs_of_pos this] at hy

                have : (1+a) * y = -1/2 := by linarith

                rcases lt_trichotomy a (-1) with (ha7 | rfl | ha8)
                . have : 1+a ≠ 0 := by linarith
                  have : y = -1/2 / (1+a) := by
                    field_simp
                    linarith
                  rw [this] at hy2
                  rw [← mul_lt_mul_left_of_neg (by linarith: 2 * (1 + a)<0)] at hy2

                  field_simp at hy2
                  rw [← mul_lt_mul_left_of_neg (by linarith: a<0)] at hy2
                  field_simp at hy2
                  ring_nf at hy2
                  have : a * a⁻¹ = 1 := by field_simp
                  rw [this] at hy2
                  have : a ^ 2 * a⁻¹ = a := by
                    rw [pow_two, mul_assoc]
                    field_simp
                  rw [this] at hy2
                  linarith

                . norm_num at this
                . have : 1+a ≠ 0 := by linarith
                  have : y = -1/2 / (1+a) := by
                    field_simp
                    linarith
                  rw [this] at hy4
                  have := mul_lt_mul_of_pos_right hy4 (by linarith: (2 * (1 + a))>0)
                  field_simp at this
                  linarith

            . field_simp at hy
              rw [abs_div] at hy
              rw [abs_of_neg (by linarith)] at hy
              rw [abs_of_neg (by linarith)] at hy
              ring_nf at hy
              have : a * a⁻¹ = 1 := by field_simp
              rw [this] at hy
              field_simp at hy
              linarith

            . have : -1 < -1 / a  := by
                rw [← mul_lt_mul_left_of_neg (by linarith: a<0)]
                field_simp
                linarith

              have : y > -1 := by linarith
              rw [abs_of_pos (by linarith)] at hy

              have : a * y + 1 < 0 := by
                rw [← mul_lt_mul_left_of_neg (by linarith: a<0)] at hy1
                field_simp at hy1
                linarith

              rw [abs_of_neg this] at hy
              have : (1-a) * y = 3/2 := by linarith
              have : y = 3/2 / (1-a) := by
                rw [← this]
                have : 1-a ≠ 0 := by linarith
                field_simp

              rw [this] at hy1
              rw [← mul_lt_mul_left_of_neg (by linarith: a<0)] at hy1
              field_simp at hy1

              have : 1-a ≠ 0 := by linarith
              have := mul_lt_mul_of_pos_right hy1 (by linarith: (2 * (1 - a))>0)
              field_simp at this
              linarith

          . left; rfl
          . rw [abs_of_pos (by linarith)] at hx2
            linarith
      . norm_num at hx1
      . rw [abs_div] at hx1
        repeat rw [abs_of_pos (by linarith)] at hx1
        ring_nf at hx1
        rw [(by field_simp: a * a⁻¹ = 1)] at hx1
        have : -1/2 ≥ a⁻¹ := by linarith
        have : a⁻¹ > 0 := by positivity
        linarith

  . intro ha

    rcases ha with rfl | rfl
    . simp
      simp [hf]
      constructor
      . use -1
        norm_num

      . intro x
        rcases lt_trichotomy x 2 with (lt2 | rfl | gt2)
        . rcases lt_trichotomy x (-1) with (lt | rfl | gt)
          . rw [abs_of_neg (by linarith)]
            rw [abs_of_pos (by linarith)]
            linarith

          . norm_num; rw [abs_of_pos (by linarith)]
          . rw [abs_of_pos (by linarith)]
            rw [abs_of_pos (by linarith)]
            linarith
        . norm_num
        . rw [abs_of_pos (by linarith)]
          rw [abs_of_neg (by linarith)]
          linarith

    . simp
      simp [hf]
      constructor
      . use 1/2
        norm_num
      . intro x
        rcases lt_trichotomy x (1/2) with (lt2 | rfl | gt2)
        . rcases lt_trichotomy x (-1) with (lt | rfl | gt)
          . rw [abs_of_neg (by linarith)]
            rw [abs_of_pos (by linarith)]
            linarith
          . norm_num
          . rw [abs_of_pos (by linarith)]
            rw [abs_of_pos (by linarith)]
            linarith
        . norm_num; rw [abs_of_pos (by linarith)]
        . rw [abs_of_pos (by linarith)]
          rw [abs_of_neg (by linarith)]
          linarith
