import Mathlib

open Real

theorem algebra_304230
  (m : ℝ)
  (h : {y : ℝ | abs (abs (y ^ 2 - 1) - 2) = m}.encard = 5) :
  m = 1 := by

  rcases lt_trichotomy m 1 with hm_le_1 | hm | hm_ge_1
  . rcases lt_trichotomy m 0 with hm_le_0 | rfl | hm_ge_0
    . have : {y | abs (|y ^ 2 - 1| - 2) = m} = ∅ := by
        ext y
        simp
        have : abs (|y ^ 2 - 1| - 2) ≥ 0 := by positivity
        linarith

      rw [this] at h
      simp at h
    . have : {y | abs (|y ^ 2 - 1| - 2) = 0} = {√3, -√3} := by
        ext y
        simp
        constructor
        . intro h
          have : abs (y ^ 2 - 1) = 2 := by linarith
          rw [abs_eq (by norm_num)] at this
          rcases this with h1 | h2
          . have : (y-√3) * (y+√3) = 0 := by
              ring_nf
              rw [sq_sqrt (by norm_num)]
              linarith
            simp at this
            rcases this with h1 | h2
            . left; linarith
            . right; linarith
          . have : y^2 ≥ 0 := by positivity
            have : y^2 - 1 ≥ -1 := by linarith
            linarith
        . intro hy
          rcases hy with rfl | rfl
          all_goals ring_nf; rw [sq_sqrt (by norm_num)]; norm_num

      rw [this] at h
      rw [Set.encard_pair] at h
      norm_num at h
      by_contra
      have : √3 > 0 := by positivity
      linarith

    . have : {y | abs (|y ^ 2 - 1| - 2) = m} = {√(3+m), -√(3+m),√(3-m), -√(3-m)} := by
        ext y
        simp
        constructor
        . intro h
          rw [abs_eq (by linarith)] at h
          rcases h with h1 | h2
          . have : |y^2 - 1| = m + 2 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√(3 + m)) * (y+√(3 + m)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . left; linarith
              . right; left; linarith
            . have : y^2 ≥ 0 := by positivity
              linarith
          . have : |y^2 - 1| = -m + 2 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√(3 - m)) * (y+√(3 - m)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . right; right; left; linarith
              . right; right; right; linarith
            . have : y^2 ≥ 0 := by positivity
              linarith

        . intro h
          rcases h with rfl | rfl | rfl | rfl
          all_goals norm_num; rw [sq_sqrt (by linarith)]; nth_rw 2 [abs_of_pos (by linarith)]
          . rw [abs_of_pos (by linarith)]
            linarith
          . rw [abs_of_pos (by linarith)]
            linarith
          . rw [abs_of_neg (by linarith)]
            linarith
          . rw [abs_of_neg (by linarith)]
            linarith

      rw [this] at h
      repeat rw [Set.encard_insert_of_not_mem] at h
      simp at h
      norm_num at h
      all_goals simp
      . by_contra h
        have : √(3 - m) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

      . by_contra h
        simp at h
        have : ¬-√(3 + m) = √(3 - m) := by
          by_contra h_contra
          have hm: √(3 - m) ≥ 0 := by positivity
          rw [← h_contra] at hm
          have : √(3 + m) ≥ 0 := by positivity
          have : √(3 + m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith
        have := h this
        rw [sqrt_inj (by linarith) (by linarith)] at this
        linarith

      . by_contra h
        simp at h
        have : ¬√(3 + m) = -√(3 + m) := by
          by_contra
          have : √(3 + m) > 0 := by positivity
          linarith

        have h := h this
        have : ¬√(3 + m) = √(3 - m) := by
          by_contra h_contra
          rw [sqrt_inj (by linarith) (by linarith)] at h_contra
          linarith

        have := h this
        have hm: √(3 + m) ≥ 0 := by positivity
        rw [this] at hm
        have : √(3 - m) ≥ 0 := by positivity
        have : √(3 - m) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

  . exact hm
  . rcases lt_trichotomy m 2 with hm_le_2 | rfl | hm_ge_2
    . have : {y | abs (|y ^ 2 - 1| - 2) = m} = {√(3+m), -√(3+m),√(3-m), -√(3-m),√(m-1), -√(m-1)} := by
        ext y
        simp
        constructor
        . intro h
          rw [abs_eq (by linarith)] at h
          rcases h with h1 | h2
          . have : |y^2 - 1| = m + 2 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√(3 + m)) * (y+√(3 + m)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . left; linarith
              . right; left; linarith
            . have : y^2 ≥ 0 := by positivity
              linarith
          . have : |y^2 - 1| = 2 - m := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√(3 - m)) * (y+√(3 - m)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . right; right; left; linarith
              . right; right; right; left; linarith
            . have : (y-√(m - 1)) * (y+√(m - 1)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . right; right; right; right; left; linarith
              . right; right; right; right; right; linarith

        . intro h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals norm_num; rw [sq_sqrt (by linarith)]
          . nth_rw 2 [abs_of_pos (by linarith)]
            nth_rw 1 [abs_of_pos (by linarith)]
            linarith
          . nth_rw 2 [abs_of_pos (by linarith)]
            nth_rw 1 [abs_of_pos (by linarith)]
            linarith
          . nth_rw 2 [abs_of_pos (by linarith)]
            nth_rw 1 [abs_of_neg (by linarith)]
            linarith
          . nth_rw 2 [abs_of_pos (by linarith)]
            nth_rw 1 [abs_of_neg (by linarith)]
            linarith
          . nth_rw 2 [abs_of_neg (by linarith)]
            nth_rw 1 [abs_of_neg (by linarith)]
            linarith
          . nth_rw 2 [abs_of_neg (by linarith)]
            nth_rw 1 [abs_of_neg (by linarith)]
            linarith

      rw [this] at h
      repeat rw [Set.encard_insert_of_not_mem] at h
      simp at h
      norm_num at h
      all_goals simp
      . by_contra h
        have : √(m - 1) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

      . by_contra h
        simp at h
        have : ¬-√(3 - m) = √(m - 1) := by
          by_contra h_contra
          have : √(m - 1) ≥ 0 := by positivity
          rw [← h_contra] at this
          have : √(3 - m) ≥ 0 := by positivity
          have : √(3 - m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith

        have := h this
        rw [sqrt_inj (by linarith) (by linarith)] at this
        linarith

      . by_contra h
        simp at h
        have : ¬√(3 - m) = -√(3 - m) := by
          by_contra h_contra
          have : √(3 - m) ≥ 0 := by positivity
          rw [h_contra] at this
          have : √(3 - m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith
        have h:= h this
        have : ¬√(3 - m) = √(m - 1) := by
          by_contra h_contra
          rw [sqrt_inj (by linarith) (by linarith)] at h_contra
          linarith
        have h:= h this
        have : √(3 - m) ≥ 0 := by positivity
        rw [h] at this
        have : √(m - 1) ≥ 0 := by positivity
        have : √(m - 1) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

      . by_contra h
        simp at h
        have : ¬-√(3 + m) = √(3 - m) := by
          by_contra h_contra
          have : √(3 - m) ≥ 0 := by positivity
          rw [← h_contra] at this
          have : √(3 + m) ≥ 0 := by positivity
          have : √(3 + m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith
        have h:= h this
        have : ¬√(3 + m) = √(3 - m) := by
          by_contra h_contra
          rw [sqrt_inj (by linarith) (by linarith)] at h_contra
          linarith
        have h:= h this
        have : ¬-√(3 + m) = √(m - 1) := by
          by_contra h_contra
          have : √(m - 1) ≥ 0 := by positivity
          rw [← h_contra] at this
          have : √(3 + m) ≥ 0 := by positivity
          have : √(3 + m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith
        have h:= h this
        rw [sqrt_inj (by linarith) (by linarith)] at h
        linarith

      . by_contra h
        simp at h
        have : ¬√(3 + m) = -√(3 + m) := by
          by_contra
          have : √(3 + m) > 0 := by positivity
          linarith
        have : ¬√(3 + m) = -√(3 + m) := by
          by_contra
          have : √(3 + m) > 0 := by positivity
          linarith
        have h:= h this
        have : ¬√(3 + m) = √(3 - m) := by
          by_contra h_contra
          rw [sqrt_inj (by linarith) (by linarith)] at h_contra
          linarith
        have h:= h this
        have : ¬√(3 + m) = -√(3 - m) := by
          by_contra h_contra
          have : √(3 + m) ≥ 0 := by positivity
          rw [h_contra] at this
          have : √(3 - m) ≥ 0 := by positivity
          have : √(3 - m) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith
        have h:= h this
        have : ¬√(3 + m) = √(m - 1) := by
          by_contra h_contra
          rw [sqrt_inj (by linarith) (by linarith)] at h_contra
          linarith
        have h:= h this
        have : √(3 + m) ≥ 0 := by positivity
        rw [h] at this
        have : √(m - 1) ≥ 0 := by positivity
        have : √(m - 1) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

    . have : {y | abs (|y ^ 2 - 1| - 2) = 2} = {√5, -√5, 1,-1} := by
        ext y
        simp
        constructor
        . intro h
          rw [abs_eq (by linarith)] at h
          rcases h with h1 | h2
          . have : |y^2 - 1| = 4 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√5) * (y+√5) = 0 := by
                ring_nf
                rw [sq_sqrt (by norm_num)]
                linarith
              simp at this
              rcases this with h1 | h2
              . left; linarith
              . right; left; linarith
            . have : y^2 ≥ 0 := by positivity
              linarith
          . have : |y^2 - 1| = 0 := by linarith
            simp at this
            have : (y-1) * (y+1) = 0 := by linarith
            simp at this
            rcases this with h1 | h2
            . right; right; left; linarith
            . right; right;right; linarith

        . intro h
          rcases h with rfl | rfl | rfl | rfl
          all_goals norm_num

      rw [this] at h
      repeat rw [Set.encard_insert_of_not_mem] at h
      simp at h
      norm_num at h
      all_goals simp
      . by_contra h
        norm_num at h
      . by_contra h
        have : √5 > 0 := by positivity
        linarith
      . by_contra h
        simp at h
        have : ¬√5 = -√5 := by
          by_contra
          have : √5 > 0 := by positivity
          linarith
        have := h this
        have : √5 > 0 := by positivity
        linarith
    . have : {y | abs (|y ^ 2 - 1| - 2) = m} = {√(3+m), -√(3+m)} := by
        ext y
        simp
        constructor
        . intro h
          rw [abs_eq (by linarith)] at h
          rcases h with h1 | h2
          . have : |y^2 - 1| = m + 2 := by linarith
            rw [abs_eq (by linarith)] at this
            rcases this with h1 | h2
            . have : (y-√(3 + m)) * (y+√(3 + m)) = 0 := by
                ring_nf
                rw [sq_sqrt (by linarith)]
                linarith
              simp at this
              rcases this with h1 | h2
              . left; linarith
              . right; linarith
            . have : y^2 ≥ 0 := by positivity
              linarith
          . have : |y^2 - 1| ≥ 0 := by positivity
            linarith

        . intro h
          rcases h with rfl | rfl
          . rw [sq_sqrt (by linarith)]
            rw [abs_eq (by linarith)]
            left
            suffices |3 + m - 1| = 2 + m by linarith
            rw [abs_eq (by linarith)]
            left
            linarith
          . norm_num
            rw [sq_sqrt (by linarith)]
            ring_nf
            rw [abs_eq (by linarith)]
            left
            suffices |2 + m| = 2 + m by linarith
            rw [abs_eq (by linarith)]
            left
            linarith

      rw [this] at h
      rw [Set.encard_pair] at h
      norm_num at h
      by_contra
      have : √(3+m) > 0 := by positivity
      linarith
