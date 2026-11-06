import Mathlib


theorem algebra_271131 : Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7) = 1 / 2 := by
  have h1 : Real.sin (Real.pi / 7) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h2 : 2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7)) = Real.sin (Real.pi / 7) := by
    have h3 : 2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7)) =
      Real.sin (2 * (Real.pi / 7)) + (Real.sin (4 * (Real.pi / 7)) - Real.sin (2 * (Real.pi / 7)) ) + (Real.sin (6 * (Real.pi / 7)) - Real.sin (4 * (Real.pi / 7)) ) := by
      have h4 : 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) = Real.sin (2 * (Real.pi / 7)) := by
        have h5 : Real.sin (2 * (Real.pi / 7)) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
          rw [show 2 * (Real.pi / 7) = 2 * (Real.pi / 7) by ring]
          rw [Real.sin_two_mul]
        linarith

      have h7 : 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) = Real.sin (4 * (Real.pi / 7)) - Real.sin (2 * (Real.pi / 7)) := by
        have h8 : 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) = Real.sin (Real.pi / 7 + 3 * Real.pi / 7) + Real.sin (Real.pi / 7 - (3 * Real.pi / 7)) := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h9 : Real.sin (Real.pi / 7 + 3 * Real.pi / 7) = Real.sin (4 * (Real.pi / 7)) := by
          ring_nf
        have h10 : Real.sin (Real.pi / 7 - (3 * Real.pi / 7)) = - Real.sin (2 * (Real.pi / 7)) := by
          have h11 : Real.pi / 7 - (3 * Real.pi / 7) = - (2 * (Real.pi / 7)) := by
            linarith [Real.pi_pos]
          rw [h11]
          have h12 : Real.sin (- (2 * (Real.pi / 7))) = - Real.sin (2 * (Real.pi / 7)) := by
            rw [Real.sin_neg]
          linarith
        rw [h8, h9, h10]
        all_goals ring

      have h13 : 2 * Real.sin (Real.pi / 7) * Real.cos (5 * Real.pi / 7) = Real.sin (6 * (Real.pi / 7)) - Real.sin (4 * (Real.pi / 7)) := by
        have h14 : 2 * Real.sin (Real.pi / 7) * Real.cos (5 * Real.pi / 7) = Real.sin (Real.pi / 7 + 5 * Real.pi / 7) + Real.sin (Real.pi / 7 - (5 * Real.pi / 7)) := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h15 : Real.sin (Real.pi / 7 + 5 * Real.pi / 7) = Real.sin (6 * (Real.pi / 7)) := by
          ring_nf
        have h16 : Real.sin (Real.pi / 7 - (5 * Real.pi / 7)) = - Real.sin (4 * (Real.pi / 7)) := by
          have h17 : Real.pi / 7 - (5 * Real.pi / 7) = - (4 * (Real.pi / 7)) := by
            linarith [Real.pi_pos]
          rw [h17]
          have h18 : Real.sin (- (4 * (Real.pi / 7))) = - Real.sin (4 * (Real.pi / 7)) := by
            rw [Real.sin_neg]
          linarith
        rw [h14, h15, h16]
        all_goals ring

      calc
        2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7))
          = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) + 2 * Real.sin (Real.pi / 7) * Real.cos (3 * Real.pi / 7) + 2 * Real.sin (Real.pi / 7) * Real.cos (5 * Real.pi / 7) := by ring
        _ = Real.sin (2 * (Real.pi / 7)) + (Real.sin (4 * (Real.pi / 7)) - Real.sin (2 * (Real.pi / 7)) ) + (Real.sin (6 * (Real.pi / 7)) - Real.sin (4 * (Real.pi / 7)) ) := by
          rw [h4, h7, h13]

    have h10 : Real.sin (6 * (Real.pi / 7)) = Real.sin (Real.pi - (Real.pi / 7)) := by
      ring_nf

    have h11 : Real.sin (Real.pi - (Real.pi / 7)) = Real.sin (Real.pi / 7) := by
      rw [Real.sin_pi_sub]

    rw [h3, h10, h11]
    all_goals ring

  have h4 : Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7) = 1 / 2 := by
    have h5 : 2 * Real.sin (Real.pi / 7) * (Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7)) = Real.sin (Real.pi / 7) := h2
    have h7 : Real.sin (Real.pi / 7) > 0 := h1
    have h8 : Real.sin (Real.pi / 7) ≠ 0 := by linarith
    have h9 : Real.cos (Real.pi / 7) + Real.cos (3 * Real.pi / 7) + Real.cos (5 * Real.pi / 7) = 1 / 2 := by
      apply (mul_left_inj' (show Real.sin (Real.pi / 7) ≠ 0 by linarith)).mp
      linarith
    linarith

  exact h4