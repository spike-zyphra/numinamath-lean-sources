import Mathlib

theorem algebra_211969:
     {n | ∃ a b : ℝ, {x : ℝ | abs (abs (abs (x - a) - 1) - 1) = abs b}.encard = n} =
     ({2, 3, 4, 6} : Set ℕ∞) := by

    ext n
    constructor
    . intro h
      rcases h with ⟨a, b, h⟩
      by_cases h1: b > 1 ∨ b < -1
      . left -- n=2
        have : |b| > 1 := by
          simp; rw [lt_abs]
          cases h1
          . left; assumption
          . right; linarith
        have : {x:ℝ | abs (abs (abs (x - a) - 1) - 1) = |b|} = {a - |b| - 2, a + |b| + 2} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro hx
            rw [abs_eq (by norm_num)] at hx
            rcases hx with hx1 | hx2
            . have : abs (|x - a| - 1) = 1 + |b| := by linarith
              rw [abs_eq (by positivity)] at this
              rcases this with hx1 | hx2
              . have : |x - a| = 2 + |b| := by linarith
                rw [abs_eq (by positivity)] at this
                rcases this with hx1 | hx2
                . have : x = a + |b| + 2 := by linarith
                  right; assumption
                . have : x = a - |b| - 2 := by linarith
                  left; assumption
              . have : |x - a| ≥ 0 := by positivity
                have : |b| ≥ 0 := by positivity
                have : |b| = 0 := by linarith
                simp at this
                rw [this] at h1
                simp at h1
                linarith
            . have : abs (|x - a| - 1) ≥ 0 := by positivity
              linarith

          . intro hx
            rcases hx with rfl | rfl
            . ring_nf
              have : abs (-2 - |b|) = - (-2 - |b|) := by rw [abs_of_neg (by linarith)]
              rw [this]; ring_nf
              have : abs (1 + |b|) = 1 + |b| := by rw [abs_of_nonneg (by linarith)]
              rw [this]; ring_nf; simp
            . ring_nf
              have : abs (2 + |b|) = 2 + |b| := by rw [abs_of_nonneg (by linarith)]
              rw [this]; ring_nf
              have : abs (1 + |b|) = 1 + |b| := by rw [abs_of_nonneg (by linarith)]
              rw [this]; ring_nf; simp

        rw [this] at h
        rw [Set.encard_pair] at h
        exact h.symm
        . -- a - |b| - 2 ≠ a + |b| + 2
          by_contra h_contra
          have : |b| ≥ 0 := by positivity
          linarith

      . right
        by_cases h2: b = 1 ∨ b = -1
        . right; left -- n=4
          have : {x:ℝ | abs (abs (|x - a| - 1) - 1) = |b|} = {a - 3, a - 1, a + 1, a + 3} := by
            have : |b| = 1 := by rw [abs_eq (by norm_num)]; exact h2
            rw [this]
            ext x
            simp only [Set.mem_setOf_eq]
            constructor
            . intro hx
              rw [abs_eq (by norm_num)] at hx
              rcases hx with hx1 | hx2
              . have : abs (|x - a| - 1) = 2 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . have : |x - a| = 3 := by linarith
                  rw [abs_eq (by norm_num)] at this
                  rcases this with hx1 | hx2
                  . right; right; right; simp; linarith
                  . left; linarith
                . have : |x - a| ≥ 0 := by positivity
                  linarith
              . have : abs (|x - a| - 1) = 0 := by linarith
                rw [abs_eq_zero] at this
                have : |x - a| = 1 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . right; right; left; linarith
                . right; left; linarith
            . intro hx
              rcases hx with rfl | rfl | rfl | rfl
              all_goals ring_nf; norm_num

          rw [this] at h
          repeat rw [Set.encard_insert_of_not_mem] at h
          norm_num at h
          exact h.symm
          all_goals simp
          all_goals constructor; all_goals by_contra; linarith
        . by_cases h3: b = 0
          . left -- n=3
            have : {x:ℝ | abs (abs (|x - a| - 1) - 1) = |b|} = {a - 2, a, a + 2} := by
              rw [h3]; simp
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro hx
                have : abs (|x - a| - 1) = 1 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . have : |x - a| = 2 := by linarith
                  rw [abs_eq (by norm_num)] at this
                  rcases this with hx1 | hx2
                  . right; right; simp; linarith
                  . left; linarith
                . have : |x - a| = 0 := by linarith
                  rw [abs_eq_zero] at this
                  right; left; linarith
              . intro hx
                rcases hx with rfl | rfl | rfl
                all_goals ring_nf; norm_num

            rw [this] at h
            repeat rw [Set.encard_insert_of_not_mem] at h
            norm_num at h
            exact h.symm
            all_goals simp
            by_contra; linarith
          . right; right; simp -- n=6
            have : {x:ℝ | abs (abs (|x - a| - 1) - 1) = |b|} = {a - 2 - b, a - b, a + 2 - b, a - 2 + b, a + b, a + 2 + b} := by
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro hx
                have : 0 < |b| := by positivity
                have : |b| < 1 := by
                  rw [abs_lt]
                  simp at h1
                  simp at h2
                  constructor
                  . exact lt_of_le_of_ne h1.2 (Ne.symm h2.2)
                  . exact lt_of_le_of_ne h1.1 h2.1

                rw [abs_eq (by norm_num)] at hx
                rcases hx with hx1 | hx2
                . have : abs (|x - a| - 1) = 1 + |b| := by linarith
                  rw [abs_eq (by linarith)] at this
                  rcases this with hx1 | hx2
                  . have : |x - a| = 2 + |b| := by linarith
                    rw [abs_eq (by linarith)] at this
                    rcases this with hx1 | hx2
                    . have : |b| = x - a - 2 := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . right; right; right; right; right; simp; linarith
                      . right; right; left; linarith
                    . have : |b| = -x + a - 2 := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . left; linarith
                      . right; right; right; left; linarith
                  . have : |x - a| ≥ 0 := by positivity
                    linarith
                . have : abs (|x - a| - 1) = 1 - |b| := by linarith
                  rw [abs_eq (by linarith)] at this
                  rcases this with hx1 | hx2
                  . have : |x - a| = 2 - |b| := by linarith
                    rw [abs_eq (by linarith)] at this
                    rcases this with hx1 | hx2
                    . have : |b| = -x + a + 2 := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . right; right; left; linarith
                      . right; right; right; right; right; simp; linarith
                    . have : |b| = x - a + 2 := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . right; right; right; left; linarith
                      . left; linarith

                  . have : |x - a| = |b| := by linarith
                    rw [abs_eq (by linarith)] at this
                    rcases this with hx1 | hx2
                    . have : |b| = x - a := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . right; right; right; right; left; linarith
                      . right; left; linarith
                    . have : |b| = -x + a := by linarith
                      apply eq_or_eq_neg_of_abs_eq at this
                      rcases this with hx1 | hx2
                      . right; left; linarith
                      . right; right; right; right; left; linarith
              . intro hx
                simp at h1
                simp at h2
                rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
                all_goals ring_nf
                . have : |-2 - b| = - (-2 - b) := by rw [abs_of_neg (by linarith)]
                  rw [this]; ring_nf
                  have : |1 + b| = 1 + b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf
                . by_cases hb : b > 0
                  . have : |(-b)| = - (-b) := by rw [abs_of_neg (by linarith)]
                    rw [this]; ring_nf
                    have : |-1 + b| = -(-1 + b) := by rw [abs_of_nonpos (by linarith)]
                    rw [this]; ring_nf; simp
                  . have : |(-b)| = -b := by rw [abs_of_nonneg (by linarith)]
                    rw [this]; ring_nf
                    have : |-1 - b| = -(-1 - b) := by rw [abs_of_nonpos (by linarith)]
                    rw [this]; ring_nf
                . have : |2 - b| = 2 - b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf
                  have : |1 - b| = 1 - b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf; simp
                . have : |-2 + b| = -(-2 + b) := by rw [abs_of_neg (by linarith)]
                  rw [this]; ring_nf
                  have : |1 - b| = 1 - b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf; simp
                . by_cases hb : b ≥ 0
                  . have : |b| = b := by rw [abs_of_nonneg (by linarith)]
                    rw [this]
                    have : |-1 + b| = -(-1 + b) := by rw [abs_of_nonpos (by linarith)]
                    rw [this]; ring_nf; norm_num; assumption
                  . have : |b| = -b := by rw [abs_of_neg (by linarith)]
                    rw [this]; ring_nf
                    have : |-1 - b| = -(-1 - b) := by rw [abs_of_nonpos (by linarith)]
                    rw [this]; ring_nf; norm_num; linarith
                . have : |2 + b| = 2 + b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf
                  have : |1 + b| = 1 + b := by rw [abs_of_nonneg (by linarith)]
                  rw [this]; ring_nf

            rw [this] at h
            repeat rw [Set.encard_insert_of_not_mem] at h
            norm_num at h
            exact h.symm
            . simp
            . simp; linarith
            . simp
              constructor
              . by_contra
                have : b = 2 := by linarith
                rw [this] at h1
                simp at h1
              . constructor
                . by_contra
                  have : b = 1 := by linarith
                  rw [this] at h2
                  simp at h2
                . by_contra
                  have : b = 0 := by linarith
                  rw [this] at h3
                  simp at h3
            . simp
              constructor
              . by_contra
                have : b = 1 := by linarith
                rw [this] at h2
                simp at h2
              . constructor
                . by_contra
                  have : b = 0 := by linarith
                  rw [this] at h3
                  simp at h3
                . by_contra
                  have : b = -1 := by linarith
                  rw [this] at h2
                  simp at h2
            . simp
              constructor
              . linarith
              . constructor
                . by_contra
                  have : b = 0 := by linarith
                  rw [this] at h3
                  simp at h3
                . constructor
                  . by_contra
                    have : b = -1 := by linarith
                    rw [this] at h2
                    simp at h2
                  . by_contra
                    have : b = -2 := by linarith
                    rw [this] at h1
                    simp at h1

    . intro hn
      rcases hn with rfl | rfl | rfl | rfl | rfl
      . use 0, 2; simp
        have : {x:ℝ | abs (abs (abs x - 1) - 1) = 2} = {4, -4} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro hx
            rw [abs_eq (by norm_num)] at hx
            rcases hx with hx1 | hx2
            . have : abs (|x| - 1) = 3 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . have : |x| = 4 := by linarith
                rw [abs_eq (by norm_num)] at this
                exact this
              . have : |x| ≥ 0 := by positivity
                linarith

            . have : abs (|x| - 1) ≥ 0 := by positivity
              linarith

          . intro hx
            rcases hx with rfl | rfl
            all_goals norm_num

        rw [this]
        rw [Set.encard_pair (by norm_num)]

      . use 0, 0; simp
        have : {x:ℝ | abs (|x| - 1) - 1 = 0} = {-2, 0, 2} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro hx
            have : abs (|x|-1) = 1 := by linarith
            rw [abs_eq (by norm_num)] at this
            rcases this with hx1 | hx2
            . have : |x| = 2 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . right; right; assumption
              . left; assumption
            . have : |x| = 0 := by linarith
              simp at this
              right; left; exact this
          . intro hx
            rcases hx with rfl | rfl | rfl
            all_goals norm_num
        rw [this]
        rw [Set.encard_insert_of_not_mem (by norm_num)]
        rw [Set.encard_pair (by norm_num)]
        norm_num


      . use 0, 1; simp
        have : {x:ℝ | abs (abs (abs x - 1) - 1) = 1} = {-1, 1, 3, -3} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro hx
            rw [abs_eq (by norm_num)] at hx
            rcases hx with hx1 | hx2
            . have : abs (|x| - 1) = 2 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . have : |x| = 3 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . right;right;left; linarith
                . right;right;right; simp;linarith
              . have : |x| ≥ 0 := by positivity
                linarith

            . have : abs (|x| - 1) = 0 := by linarith
              rw [abs_eq_zero] at this
              have : |x| = 1 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . right;left; linarith
              . left; linarith

          . intro hx
            rcases hx with rfl | rfl | rfl | rfl
            all_goals norm_num

        rw [this]
        repeat rw [Set.encard_insert_of_not_mem (by norm_num)]
        simp
        norm_num

      . use 1/2, 1/2; simp; rw [abs_of_pos (by norm_num)]; norm_num
        have : {x:ℝ | abs (abs (abs (x - 1/2) - 1) - 1) = 1/2} = {-2,-1,0,1,2,3} := by
          ext x
          simp only [Set.mem_setOf_eq]

          constructor
          . intro hx
            rw [abs_eq (by norm_num)] at hx
            rcases hx with hx1 | hx2
            . have : abs (|x - 1 / 2| - 1) = 3/2 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . have : |x - 1 / 2| = 5 / 2 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . right;right;right;right;right;simp;linarith
                . left; linarith
              . have : |x - 1 / 2| ≥ 0 := by positivity
                linarith

            . have : abs (|x - 1 / 2| - 1) = 1/2 := by linarith
              rw [abs_eq (by norm_num)] at this
              rcases this with hx1 | hx2
              . have : |x - 1 / 2| = 3 / 2 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . right;right;right;right;left; linarith
                . right;left; linarith
              . have : |x - 1 / 2| = 1 / 2 := by linarith
                rw [abs_eq (by norm_num)] at this
                rcases this with hx1 | hx2
                . right;right;right;left; linarith
                . right;right;left; linarith

          . intro hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
            all_goals
            . norm_num; nth_rw 3 [abs_of_pos (by norm_num)]
              norm_num; nth_rw 2 [abs_of_pos (by norm_num)]
              norm_num

        rw [this]
        repeat rw [Set.encard_insert_of_not_mem (by norm_num)]
        simp
        norm_num
