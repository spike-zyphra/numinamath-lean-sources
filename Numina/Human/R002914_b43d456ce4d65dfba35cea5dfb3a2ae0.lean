import Mathlib

theorem algebra_129596 (a : ℝ) :
  {(x, y) : ℝ × ℝ | abs (x - 1) + abs (y - a) = 1 ∧ y = -2 * abs (x - 1) - 1}.encard = 3 ↔
  a = -2:= by
  constructor
  . intro h_card
    simp at h_card

    by_cases h1: a > 0
    . have : {x: ℝ × ℝ | |x.1 - 1| + |x.2 - a| = 1 ∧ x.2 = -(2 * |x.1 - 1|) - 1} = ∅ := by
        ext x
        simp
        intro hx
        by_contra h2
        have : |x.1 - 1| ≥ 0 := by positivity
        have : x.2 ≤ -1 := by linarith
        have : |x.2 - a| ≤ 1 := by rw [← hx]; simp
        have : x.2 - a < 0 := by linarith
        have : |x.2 - a| = a - x.2 := by rw [abs_of_neg (by linarith)]; simp
        linarith

      rw [this] at h_card
      simp at h_card

    . by_cases h2: a > -2
      . have : {x: ℝ × ℝ | |x.1 - 1| + |x.2 - a| = 1 ∧ x.2 = -(2 * |x.1 - 1|) - 1} = {((3-a)/3, (2*a-3)/3), ((3+a)/3, (2*a-3)/3)} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro ⟨hx1, hx2⟩
            by_cases h3: x.1 ≥ 1
            . rw [abs_of_nonneg (by linarith)] at hx1
              rw [abs_of_nonneg (by linarith)] at hx2
              by_cases h4: x.2 ≥ a
              . rw [abs_of_nonneg (by linarith)] at hx1
                linarith
              . rw [abs_of_neg (by linarith)] at hx1
                have h_1: x.1 = (3 - a) / 3 := by linarith
                have h_2: x.2 = (2 * a - 3) / 3 := by linarith
                left
                rw [← h_2,← h_1]
            . simp at h3
              rw [abs_of_neg (by linarith)] at hx1
              rw [abs_of_neg (by linarith)] at hx2
              by_cases h4: x.2 ≥ a
              . rw [abs_of_nonneg (by linarith)] at hx1
                linarith
              . rw [abs_of_neg (by linarith)] at hx1
                have h_1: x.1 = (3 + a) / 3 := by linarith
                have h_2: x.2 = (2 * a - 3) / 3 := by linarith
                right
                rw [← h_2,← h_1]
                simp

          . intro hx
            simp at h1
            rcases hx with rfl | rfl
            . simp
              rw [abs_of_nonneg (by linarith)]
              rw [abs_of_neg (by linarith)]
              ring_nf
              norm_num
            . simp
              rw [abs_of_nonpos (by linarith)]
              rw [abs_of_neg (by linarith)]
              ring_nf
              norm_num

        rw [this] at h_card

        by_cases h_neq: ((3 - a) / 3, (2 * a - 3) / 3) ≠ ((3 + a) / 3, (2 * a - 3) / 3)
        . rw [Set.encard_pair h_neq] at h_card
          norm_num at h_card
        . simp at h_neq
          rw [h_neq] at h_card
          simp at h_card

      . by_cases h3: a ≥ -3
        . have : {x: ℝ × ℝ | |x.1 - 1| + |x.2 - a| = 1 ∧ x.2 = -(2 * |x.1 - 1|) - 1} = {((3+a)/3, (2*a-3)/3),(3+a,3+2*a),(-1-a,3+2*a), ((3-a)/3, (2*a-3)/3)} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor
            . intro ⟨hx1, hx2⟩
              by_cases h4: x.1 ≥ 1
              . rw [abs_of_nonneg (by linarith)] at hx1
                rw [abs_of_nonneg (by linarith)] at hx2
                by_cases h5: x.2 ≥ a
                . rw [abs_of_nonneg (by linarith)] at hx1
                  have h_1: x.1 = -1 - a := by linarith
                  have h_2: x.2 = 3 + 2 * a := by linarith
                  right; right; left
                  rw [← h_2,← h_1]
                . simp at h5
                  rw [abs_of_neg (by linarith)] at hx1
                  have h_1: x.1 = (3 - a) / 3 := by linarith
                  have h_2: x.2 = (2 * a - 3) / 3 := by linarith
                  right; right; right
                  rw [← h_2,← h_1]
                  simp
              . simp at h4
                rw [abs_of_neg (by linarith)] at hx1
                rw [abs_of_neg (by linarith)] at hx2
                by_cases h5: x.2 ≥ a
                . rw [abs_of_nonneg (by linarith)] at hx1
                  have h_1: x.1 = (3 + a):= by linarith
                  have h_2: x.2 = (3 + 2 * a):= by linarith
                  right; left
                  rw [← h_2, ← h_1]
                . rw [abs_of_neg (by linarith)] at hx1
                  have h_1: x.1 = (3 + a) / 3 := by linarith
                  have h_2: x.2 = (2 * a - 3) / 3 := by linarith
                  left
                  rw [← h_2,← h_1]
            . intro hx
              simp at h2
              rcases hx with rfl | rfl | rfl | rfl
              . simp
                rw [abs_of_neg (by linarith)]
                rw [abs_of_nonpos (by linarith)]
                ring_nf
                norm_num
              . simp
                rw [abs_of_nonpos (by linarith)]
                rw [abs_of_nonneg (by linarith)]
                ring_nf
                norm_num
              . simp
                rw [abs_of_nonneg (by linarith)]
                rw [abs_of_nonneg (by linarith)]
                ring_nf
                norm_num
              . simp
                rw [abs_of_nonneg (by linarith)]
                rw [abs_of_nonpos (by linarith)]
                ring_nf
                norm_num
          rw [this] at h_card

          by_cases h4: a = -3 ∨ a = -2
          . rcases h4 with rfl | rfl
            . simp at h_card
              norm_num at h_card
              rw [Set.encard_pair (by norm_num)] at h_card
              contradiction
            . rfl
          . rw [Set.encard_insert_of_not_mem] at h_card
            rw [Set.encard_insert_of_not_mem] at h_card

            have : (-1 - a, 3 + 2 * a) ≠ ((3 - a) / 3, (2 * a - 3) / 3) := by
              by_contra h
              simp at h
              have : a = -3 := by linarith
              rw [this] at h4
              simp at h4
            rw [Set.encard_pair this] at h_card
            norm_num at h_card

            -- (3 + a, 3 + 2 * a) ∉ {(-1 - a, 3 + 2 * a), ((3 - a) / 3, (2 * a - 3) / 3)}
            by_contra h
            cases' h with h h'
            . simp at h
              have : a = -2 := by linarith
              rw [this] at h4
              simp at h4
            . simp at h'
              have : a = -2 := by linarith
              rw [this] at h4
              simp at h4

            -- ((3 + a) / 3, (2 * a - 3) / 3) ∉ {(3 + a, 3 + 2 * a), (-1 - a, 3 + 2 * a), ((3 - a) / 3, (2 * a - 3) / 3)}
            by_contra h
            cases' h with h h'
            . simp at h
              have : a = -3 := by linarith
              rw [this] at h4
              simp at h4
            . simp at h'
              cases' h' with h' h''
              . linarith
              . linarith

        . have : {x: ℝ × ℝ | |x.1 - 1| + |x.2 - a| = 1 ∧ x.2 = -(2 * |x.1 - 1|) - 1} = ∅ := by
            ext x
            simp
            intro hx
            by_contra h
            simp at h3
            by_cases h4: x.1 ≥ 1
            . rw [abs_of_nonneg (by linarith)] at hx
              rw [abs_of_nonneg (by linarith)] at h
              by_cases h5: x.2 ≥ a
              . rw [abs_of_nonneg (by linarith)] at hx
                linarith
              . rw [abs_of_neg (by linarith)] at hx
                linarith
            . simp at h4
              rw [abs_of_neg (by linarith)] at hx
              rw [abs_of_neg (by linarith)] at h
              by_cases h5: x.2 ≥ a
              . rw [abs_of_nonneg (by linarith)] at hx
                linarith
              . rw [abs_of_neg (by linarith)] at hx
                linarith

          rw [this] at h_card
          simp at h_card

  . intro ha
    rw [ha]
    simp
    have h_sol : {x: ℝ × ℝ | |x.1 - 1| + |x.2 + 2| = 1 ∧ x.2 = -(2 * |x.1 - 1|) - 1} =  {(1/3, -7/3), (1, -1), (5/3, -7/3)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      . intro ⟨hx1, hx2⟩
        by_cases h1: x.1 ≥ 1
        . rw [abs_of_nonneg (by linarith)] at hx1
          rw [abs_of_nonneg (by linarith)] at hx2
          by_cases h2: x.2 ≥ -2
          . rw [abs_of_nonneg (by linarith)] at hx1
            have h_1: x.1 = 1 := by linarith
            have h_2: x.2 = -1 := by linarith
            right; left;
            rw [← h_2,← h_1]

          . rw [abs_of_neg (by linarith)] at hx1
            have h_1: x.1 = 5 / 3 := by linarith
            have h_2: x.2 = -7 / 3 := by linarith
            right; right;
            rw [← h_2,← h_1]
            simp

        . rw [abs_of_neg (by linarith)] at hx1
          rw [abs_of_neg (by linarith)] at hx2
          by_cases h2: x.2 ≥ -2
          . rw [abs_of_nonneg (by linarith)] at hx1
            have h_1: x.1 = 1 := by linarith
            have h_2: x.2 = -1 := by linarith
            right; left;
            rw [← h_2,← h_1]
          . rw [abs_of_neg (by linarith)] at hx1
            have h_1: x.1 = 1 / 3 := by linarith
            have h_2: x.2 = -7 / 3 := by linarith
            left
            rw [← h_2,← h_1]

      . intro hx

        rcases hx with rfl | rfl | rfl | rfl
        all_goals simp; ring_nf; norm_num; repeat rw [abs_of_pos (by positivity)]; norm_num

    rw [h_sol]
    rw [Set.encard_insert_of_not_mem]
    rw [Set.encard_pair]
    norm_num
    all_goals simp; norm_num
