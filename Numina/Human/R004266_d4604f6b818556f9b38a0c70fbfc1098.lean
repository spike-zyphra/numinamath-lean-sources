import Mathlib

open Real

theorem algebra_246821 (a : ℝ) :
    (∃! x : ℝ, abs (abs (x + 2) - abs (2 - x) + 2) = 2 - a) ↔
    (-4 < a ∧ a < 0) ∨ a = 2 := by
    constructor
    . intro hx
      rcases hx with ⟨x, hx1, hx2⟩
      by_cases ha1 : a > 2
      . have : abs (|x + 2| - |2 - x| + 2) ≥ 0 := by positivity
        linarith
      . by_cases ha2 : a = 2
        . right; exact ha2
        . left
          by_cases ha3 : a > 0
          . simp at ha1
            have : a < 2 := lt_of_le_of_ne ha1 ha2
            have h1 := hx2 (-2+a/2)
            have h2 := hx2 (-a/2)
            simp at h1 h2
            nth_rw 2 [abs_of_pos (by linarith)] at h1
            nth_rw 2 [abs_of_pos (by linarith)] at h1
            rw [abs_of_neg (by linarith)] at h1
            ring_nf at h1
            simp at h1

            nth_rw 2 [abs_of_pos (by linarith)] at h2
            nth_rw 2 [abs_of_pos (by linarith)] at h2
            rw [abs_of_pos (by linarith)] at h2
            ring_nf at h2
            simp at h2

            rw [← h1] at h2
            linarith

          . by_cases ha4 : a = 0
            . have h1:= hx2 0
              have h2:= hx2 (-2)

              rw [ha4] at h1
              rw [ha4] at h2
              simp at h1 h2
              rw [← h1] at h2
              norm_num at h2

            . by_cases ha5 : a = -4
              . have h1 := hx2 2
                have h2 := hx2 3

                rw [ha5] at h1
                rw [ha5] at h2
                simp at h1 h2
                norm_num at h1 h2
                rw [← h1] at h2
                linarith

              . by_contra h_contra
                have ha6 : a < -4 := by
                  by_contra h
                  simp at h h_contra
                  have : -4 < a := lt_of_le_of_ne h (Ne.symm ha5)
                  have := h_contra this
                  have : 0 < a := lt_of_le_of_ne this (Ne.symm ha4)
                  contradiction

                suffices abs (|x + 2| - |2 - x| + 2) ≤ 6 by linarith
                by_cases hx1 : x ≥ 2
                . nth_rw 2 [abs_of_pos (by linarith)]
                  nth_rw 2 [abs_of_nonpos (by linarith)]
                  norm_num
                . simp at hx1
                  by_cases hx2 : x ≥ -1
                  . nth_rw 2 [abs_of_nonneg (by linarith)]
                    nth_rw 2 [abs_of_nonneg (by linarith)]
                    rw [abs_of_nonneg (by linarith)]
                    linarith
                  . by_cases hx3 : x ≥ -2
                    . simp at hx2
                      nth_rw 2 [abs_of_nonneg (by linarith)]
                      nth_rw 2 [abs_of_nonneg (by linarith)]
                      ring_nf
                      rw [abs_of_neg (by linarith)]
                      linarith
                    . simp at hx3
                      nth_rw 2 [abs_of_neg (by linarith)]
                      nth_rw 2 [abs_of_pos (by linarith)]
                      ring_nf
                      norm_num

    . intro ha
      rcases ha with ha | rfl
      . use -a / 2
        simp
        constructor
        . nth_rw 2 [abs_of_pos (by linarith)]
          nth_rw 2 [abs_of_pos (by linarith)]
          rw [abs_of_pos (by linarith)]
          ring_nf
        . intro y hy
          by_cases hy1: y ≥ 2
          . nth_rw 2 [abs_of_nonneg (by linarith)] at hy
            nth_rw 2 [abs_of_nonpos (by linarith)] at hy
            norm_num at hy
            linarith
          . simp at hy1
            nth_rw 3 [abs_of_pos (by linarith)] at hy
            by_cases hy2: y ≥ -1
            . nth_rw 2 [abs_of_nonneg (by linarith)] at hy
              rw [abs_of_nonneg (by linarith)] at hy
              linarith
            . simp at hy2
              by_cases hy3: y ≥ -2
              . nth_rw 2 [abs_of_nonneg (by linarith)] at hy
                rw [abs_of_neg (by linarith)] at hy
                linarith
              . simp at hy3
                nth_rw 2 [abs_of_neg (by linarith)] at hy
                ring_nf at hy
                norm_num at hy
                have : a = 0 := by linarith
                rw [this] at ha
                norm_num at ha

      . use -1
        simp
        constructor
        . norm_num
        . intro y hy
          by_cases hy1: y ≥ 2
          . rw [abs_of_nonneg (by linarith)] at hy
            rw [abs_of_nonpos (by linarith)] at hy
            norm_num at hy
          . simp at hy1
            nth_rw 2 [abs_of_pos (by linarith)] at hy
            by_cases hy2: y ≥ -2
            . rw[abs_of_nonneg (by linarith)] at hy
              linarith
            . rw [abs_of_nonpos (by linarith)] at hy
              linarith
