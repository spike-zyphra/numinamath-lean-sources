import Mathlib

theorem algebra_307587 : Real.cos (Real.pi / 11) - Real.cos (2 * Real.pi / 11) + Real.cos (3 * Real.pi / 11) -
    Real.cos (4 * Real.pi / 11) + Real.cos (5 * Real.pi / 11) = 1 / 2 := by
  have h1 : Real.sin (Real.pi / 11) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    . linarith [Real.pi_pos]
    . linarith [Real.pi_pos]

  have h3 : Real.sin (Real.pi / 11) * (Real.cos (Real.pi / 11) - Real.cos (2 * Real.pi / 11) + Real.cos (3 * Real.pi / 11) - Real.cos (4 * Real.pi / 11) + Real.cos (5 * Real.pi / 11)) * 2 = Real.sin (Real.pi / 11) := by
    have h5 : Real.sin (Real.pi / 11) * Real.cos (Real.pi / 11) * 2 = Real.sin (2 * Real.pi / 11) := by
      have h9 : Real.sin (Real.pi / 11) * Real.cos (Real.pi / 11) = (Real.sin (2 * Real.pi / 11)) / 2 := by
        have h10 : Real.sin (2 * Real.pi / 11) = 2 * Real.sin (Real.pi / 11) * Real.cos (Real.pi / 11) := by
          rw [show 2 * Real.pi / 11 = 2 * (Real.pi / 11) by ring]
          rw [Real.sin_two_mul]
        linarith
      linarith

    have h8 : Real.sin (Real.pi / 11) * Real.cos (2 * Real.pi / 11) * 2 = Real.sin (3 * Real.pi / 11) - Real.sin (Real.pi / 11) := by
      have h9 : Real.sin (Real.pi / 11) * Real.cos (2 * Real.pi / 11) = (Real.sin (3 * Real.pi / 11) - Real.sin (Real.pi / 11)) / 2 := by
        have h10 : Real.sin (Real.pi / 11) * Real.cos (2 * Real.pi / 11) = (Real.sin (Real.pi / 11 + 2 * Real.pi / 11) + Real.sin (Real.pi / 11 - 2 * Real.pi / 11)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h11 : Real.pi / 11 + 2 * Real.pi / 11 = 3 * Real.pi / 11 := by ring
        have h12 : Real.pi / 11 - 2 * Real.pi / 11 = - (Real.pi / 11) := by ring
        rw [h11, h12] at h10
        have h13 : Real.sin (- (Real.pi / 11)) = - Real.sin (Real.pi / 11) := by
          rw [Real.sin_neg]
        rw [h13] at h10
        linarith
      linarith

    have h13 : Real.sin (Real.pi / 11) * Real.cos (3 * Real.pi / 11) * 2 = Real.sin (4 * Real.pi / 11) - Real.sin (2 * Real.pi / 11) := by
      have h14 : Real.sin (Real.pi / 11) * Real.cos (3 * Real.pi / 11) = (Real.sin (4 * Real.pi / 11) - Real.sin (2 * Real.pi / 11)) / 2 := by
        have h15 : Real.sin (Real.pi / 11) * Real.cos (3 * Real.pi / 11) = (Real.sin (Real.pi / 11 + 3 * Real.pi / 11) + Real.sin (Real.pi / 11 - 3 * Real.pi / 11)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h16 : Real.pi / 11 + 3 * Real.pi / 11 = 4 * Real.pi / 11 := by ring
        have h17 : Real.pi / 11 - 3 * Real.pi / 11 = - (2 * Real.pi / 11) := by ring
        rw [h16, h17] at h15
        have h18 : Real.sin (- (2 * Real.pi / 11)) = - Real.sin (2 * Real.pi / 11) := by
          rw [Real.sin_neg]
        rw [h18] at h15
        linarith
      linarith

    have h19 : Real.sin (Real.pi / 11) * Real.cos (4 * Real.pi / 11) * 2 = Real.sin (5 * Real.pi / 11) - Real.sin (3 * Real.pi / 11) := by
      have h20 : Real.sin (Real.pi / 11) * Real.cos (4 * Real.pi / 11) = (Real.sin (5 * Real.pi / 11) - Real.sin (3 * Real.pi / 11)) / 2 := by
        have h21 : Real.sin (Real.pi / 11) * Real.cos (4 * Real.pi / 11) = (Real.sin (Real.pi / 11 + 4 * Real.pi / 11) + Real.sin (Real.pi / 11 - 4 * Real.pi / 11)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h22 : Real.pi / 11 + 4 * Real.pi / 11 = 5 * Real.pi / 11 := by ring
        have h23 : Real.pi / 11 - 4 * Real.pi / 11 = - (3 * Real.pi / 11) := by ring
        rw [h22, h23] at h21
        have h24 : Real.sin (- (3 * Real.pi / 11)) = - Real.sin (3 * Real.pi / 11) := by
          rw [Real.sin_neg]
        rw [h24] at h21
        linarith
      linarith

    have h25 : Real.sin (Real.pi / 11) * Real.cos (5 * Real.pi / 11) * 2 = Real.sin (6 * Real.pi / 11) - Real.sin (4 * Real.pi / 11) := by
      have h26 : Real.sin (Real.pi / 11) * Real.cos (5 * Real.pi / 11) = (Real.sin (6 * Real.pi / 11) - Real.sin (4 * Real.pi / 11)) / 2 := by
        have h27 : Real.sin (Real.pi / 11) * Real.cos (5 * Real.pi / 11) = (Real.sin (Real.pi / 11 + 5 * Real.pi / 11) + Real.sin (Real.pi / 11 - 5 * Real.pi / 11)) / 2 := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have h28 : Real.pi / 11 + 5 * Real.pi / 11 = 6 * Real.pi / 11 := by ring
        have h29 : Real.pi / 11 - 5 * Real.pi / 11 = - (4 * Real.pi / 11) := by ring
        rw [h28, h29] at h27
        have h30 : Real.sin (- (4 * Real.pi / 11)) = - Real.sin (4 * Real.pi / 11) := by
          rw [Real.sin_neg]
        rw [h30] at h27
        linarith
      linarith

    have h31 : Real.sin (6 * Real.pi / 11) = Real.sin (5 * Real.pi / 11) := by
      have h32 : 6 * Real.pi / 11 = Real.pi - (5 * Real.pi / 11) := by ring
      rw [h32]
      rw [Real.sin_pi_sub]

    -- Now combine all terms
    calc
      Real.sin (Real.pi / 11) * (Real.cos (Real.pi / 11) - Real.cos (2 * Real.pi / 11) + Real.cos (3 * Real.pi / 11) - Real.cos (4 * Real.pi / 11) + Real.cos (5 * Real.pi / 11)) * 2
        = Real.sin (Real.pi / 11) * Real.cos (Real.pi / 11) * 2 - Real.sin (Real.pi / 11) * Real.cos (2 * Real.pi / 11) * 2 + Real.sin (Real.pi / 11) * Real.cos (3 * Real.pi / 11) * 2 - Real.sin (Real.pi / 11) * Real.cos (4 * Real.pi / 11) * 2 + Real.sin (Real.pi / 11) * Real.cos (5 * Real.pi / 11) * 2 := by ring
      _ = Real.sin (2 * Real.pi / 11) - (Real.sin (3 * Real.pi / 11) - Real.sin (Real.pi / 11)) + (Real.sin (4 * Real.pi / 11) - Real.sin (2 * Real.pi / 11)) - (Real.sin (5 * Real.pi / 11) - Real.sin (3 * Real.pi / 11)) + (Real.sin (6 * Real.pi / 11) - Real.sin (4 * Real.pi / 11)) := by
          rw [h5, h8, h13, h19, h25]
      _ = Real.sin (Real.pi / 11) := by
          rw [h31]
          ring

  -- Now solve for the sum
  have h4 : Real.sin (Real.pi / 11) * (2 * (Real.cos (Real.pi / 11) - Real.cos (2 * Real.pi / 11) + Real.cos (3 * Real.pi / 11) - Real.cos (4 * Real.pi / 11) + Real.cos (5 * Real.pi / 11)) ) = Real.sin (Real.pi / 11) := by
    linarith

  -- Now, since $\sin\frac{\pi}{11} \neq 0$, we can divide both sides by $\sin\frac{\pi}{11}$.
  have h33 : 2 * (Real.cos (Real.pi / 11) - Real.cos (2 * Real.pi / 11) + Real.cos (3 * Real.pi / 11) - Real.cos (4 * Real.pi / 11) + Real.cos (5 * Real.pi / 11)) = 1 := by
    apply (mul_left_inj' h1).mp
    linarith

  -- Now solve for the sum.
  linarith