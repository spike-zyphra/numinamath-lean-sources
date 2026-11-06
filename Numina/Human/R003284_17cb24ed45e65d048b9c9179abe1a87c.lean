import Mathlib

set_option maxHeartbeats 600000

/- Determine all values of the real parameter $a$,
for which the equation $2 \cdot|2 \cdot| x\left|-a^{2}\right|=x-a$ has exactly three real solutions.
 -/

theorem algebra_166659:
  {a: ℝ | {x: ℝ | 2 * abs (2 * abs x - a ^ 2) = x - a}.encard = 3} = {-2, -1/2} := by

  ext a
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    by_contra! n
    set s:= {x: ℝ | 2 * abs (2 * abs x - a ^ 2) = x - a}
    have hs: s.Finite := by
        apply Set.finite_of_encard_eq_coe at h
        tauto

    -- we first show that a ≠ 0
    have u: a ≠ 0 := by
        by_contra! o
        have i: s = {0} := by
            simp [s, o]
            ext x
            simp
            by_cases y: 0 ≤ x
            .
                rw [show |x| = x by apply abs_of_nonneg; linarith]
                rw [show |2 * x| = 2 * x by apply abs_of_nonneg; linarith]
                constructor
                .
                    intro f
                    linarith
                .
                    intro f
                    linarith
            .
                rw [show |x| = -x by apply abs_of_nonpos; linarith]
                rw [show |2 * -x| = 2 * -x by apply abs_of_nonneg; linarith]
                constructor
                .
                    intro f
                    linarith
                .
                    intro f
                    linarith
        simp [i] at h


    by_cases l: a < -2

    -- case when a < -2
    .
        -- we show that the card is at most 2
        have o: s ⊆ {(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5} := by
            simp [s]
            intro x hx
            simp at hx
            simp
            by_cases r: x < 0
            .
                rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
                by_cases r1: 2 * -x - a ^ 2 < 0
                .
                    rw [show |2 * -x - a ^ 2| = -(2 * -x - a ^ 2) by apply abs_of_nonpos; linarith] at hx
                    nlinarith
                .
                    rw [show |2 * -x - a ^ 2| = (2 * -x - a ^ 2) by apply abs_of_nonneg; linarith] at hx
                    nlinarith
            .
                simp at r
                rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
                by_cases r1: 2 * x - a ^ 2 < 0
                .
                    rw [show |2 * x - a ^ 2| = -(2 * x - a ^ 2) by apply abs_of_nonpos; linarith] at hx
                    right
                    nlinarith
                .
                    rw [show |2 * x - a ^ 2| = (2 * x - a ^ 2) by apply abs_of_nonneg; linarith] at hx
                    left
                    nlinarith
        apply Set.Finite.eq_of_subset_of_encard_le at o
        simp [h] at o
        have t: ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard ≤ 2 := by
            rw [Set.encard_insert_of_not_mem]
            simp
            norm_num
            simp
            nlinarith
        have t': ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard ≤ 3 := by
            rw [Set.encard_insert_of_not_mem]
            simp
            norm_num
            simp
            nlinarith
        apply o at t'
        replace t': s.encard = ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard := by
            rw [o]
            rw [Set.encard_insert_of_not_mem]
            simp
            norm_num
            simp
            nlinarith
        simp [h] at t'
        rw [← t'] at t
        norm_num at t
        simp

    .
        simp at l
        replace l: -2 < a := by
            by_contra! o
            replace o: a = -2 := by linarith
            tauto
        by_cases r: a < -1/2
        .
            -- case when -2 < a < -1/2
            -- we show that the encard is 4
            set t: Set ℝ := {(a - 2 * a ^ 2) / 5, - (2 * a ^ 2 + a) / 3, (2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}
            have ht: t ⊆ s:= by
                simp [t, s]
                intro x hx
                simp at hx
                replace l: -2 < a := by
                    by_contra! o
                    replace o: a = -2 := by linarith
                    tauto
                simp
                rcases hx with q | q | q | q
                .
                    rw [show |x| = -x by apply abs_of_nonpos; nlinarith]
                    rw [show |2 * -x - a ^ 2| = 2 * -x - a ^ 2 by apply abs_of_nonneg; nlinarith]
                    linarith
                .
                    rw [show |x| = -x by apply abs_of_nonpos; nlinarith]
                    rw [show |2 * -x - a ^ 2| = -(2 * -x - a ^ 2) by apply abs_of_nonpos; nlinarith]
                    linarith
                .
                    rw [show |x| = x by apply abs_of_nonneg; nlinarith]
                    rw [show |2 * x - a ^ 2| = (2 * x - a ^ 2) by apply abs_of_nonneg; nlinarith]
                    linarith
                .
                    rw [show |x| = x by apply abs_of_nonneg; nlinarith]
                    rw [show |2 * x - a ^ 2| = -(2 * x - a ^ 2) by apply abs_of_nonpos; nlinarith]
                    linarith
            have f: t.encard = 4 := by

                simp [t]
                repeat rw [Set.encard_insert_of_not_mem]
                simp
                norm_num
                simp
                nlinarith
                simp
                constructor
                .
                    nlinarith
                .
                    nlinarith
                .
                    simp
                    refine ⟨?_, (by nlinarith), (by nlinarith)⟩
                    nlinarith

            apply Set.Finite.eq_of_subset_of_encard_le at ht
            have i: s.encard ≤ t.encard := by
                simp [f, h]
                norm_num
            apply ht at i
            rw [i] at f
            rw [f] at h
            norm_num at h
            apply Set.finite_of_encard_eq_coe at f
            tauto

        -- case -1/2 < a, we show that the card is at most 2
        .
            by_cases f: a < 0

            -- case -1/2 < a < 0
            .

                replace r: -1/2 < a := by
                    by_contra! o
                    replace o: a = -1/2 := by
                        linarith
                    tauto
                clear l n
                set t: Set ℝ := {(a - 2 * a ^ 2) / 5, (2 * a ^ 2 - a) / 3}
                have o: s ⊆ t := by
                    simp [s, t]
                    intro x hx
                    simp at hx
                    simp
                    by_cases k1: x < -a^2 / 2
                    .
                        rw [show |x| = -x by apply abs_of_nonpos; nlinarith] at hx
                        rw [show |2 * -x - a ^ 2| = 2 * -x - a ^ 2 by apply abs_of_nonneg; nlinarith] at hx
                        left
                        nlinarith
                    .
                        by_cases k2: x < 0
                        .
                            simp at k1
                            rw [show |x| = -x by apply abs_of_nonpos; nlinarith] at hx
                            rw [show |2 * -x - a ^ 2| = -(2 * -x - a ^ 2) by apply abs_of_nonpos; nlinarith] at hx
                            nlinarith
                        .
                            by_cases k3: x < a^2 / 2
                            .
                                rw [show |x| = x by apply abs_of_nonneg; nlinarith] at hx
                                rw [show |2 * x - a ^ 2| = -(2 * x - a ^ 2) by apply abs_of_nonpos; nlinarith] at hx
                                simp at k1 k2
                                clear k1 hs h
                                ring_nf at hx
                                replace hx: x = (2 * a ^ 2 + a) / 5 := by
                                    nlinarith
                                simp [hx] at k2 k3
                                clear hx
                                clear_value s t
                                have s1: 0 ≤ a := by nlinarith
                                clear k2
                                nlinarith
                            .
                                right
                                rw [show |x| = x by apply abs_of_nonneg; nlinarith] at hx
                                rw [show |2 * x - a ^ 2| = (2 * x - a ^ 2) by apply abs_of_nonneg; nlinarith] at hx
                                nlinarith

                have i: t.encard = 2 := by
                    simp [t]
                    rw [Set.encard_insert_of_not_mem]
                    simp
                    norm_num
                    simp
                    nlinarith
                apply Set.Finite.eq_of_subset_of_encard_le at o
                have j: t.encard ≤ s.encard := by
                    simp [i, h]
                    norm_num
                simp [j] at o
                rw [o] at h
                rw [h] at i
                norm_num at i
                simp [t]

            .
                -- finally for 0 ≤ a
                simp at f
                have o: s ⊆ {(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5} := by
                    simp [s]
                    intro x hx
                    simp at hx
                    simp
                    by_cases r: x < 0
                    .
                        rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
                        by_cases r1: 2 * -x - a ^ 2 < 0
                        .
                            rw [show |2 * -x - a ^ 2| = -(2 * -x - a ^ 2) by apply abs_of_nonpos; linarith] at hx
                            nlinarith
                        .
                            rw [show |2 * -x - a ^ 2| = (2 * -x - a ^ 2) by apply abs_of_nonneg; linarith] at hx
                            nlinarith
                    .
                        simp at r
                        rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
                        by_cases r1: 2 * x - a ^ 2 < 0
                        .
                            rw [show |2 * x - a ^ 2| = -(2 * x - a ^ 2) by apply abs_of_nonpos; linarith] at hx
                            right
                            nlinarith
                        .
                            rw [show |2 * x - a ^ 2| = (2 * x - a ^ 2) by apply abs_of_nonneg; linarith] at hx
                            left
                            nlinarith
                apply Set.Finite.eq_of_subset_of_encard_le at o
                simp [h] at o
                have t: ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard ≤ 2 := by
                    by_cases o: a = 2
                    .
                        simp [o]
                        norm_num
                    .
                        rw [Set.encard_insert_of_not_mem]
                        simp
                        norm_num
                        simp
                        by_contra! f
                        replace f: a * (a - 2) = 0 := by
                            nlinarith
                        simp at f
                        rcases f with f | f
                        .
                            tauto
                        .
                            replace f: a = 2 := by linarith
                            tauto
                have t': ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard ≤ 3 := by
                    by_cases o: a = 2
                    .
                        simp [o]
                        norm_num
                    .
                        rw [Set.encard_insert_of_not_mem]
                        simp
                        norm_num
                        simp
                        by_contra! f
                        replace f: a * (a - 2) = 0 := by
                            nlinarith
                        simp at f
                        rcases f with f | f
                        .
                            tauto
                        .
                            replace f: a = 2 := by linarith
                            tauto
                apply o at t'
                replace t': s.encard = ({(2 * a ^ 2 - a) / 3, (2 * a ^ 2 + a) / 5}: Set ℝ).encard := by
                  rw [t']
                simp [h] at t'
                rw [← t'] at t
                norm_num at t
                simp



  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h

    -- case when a = -2
    .
        simp [h]
        suffices {x: ℝ | 2 * |2 * |x| - 2 ^ 2| = x + 2} = {-2, 10 / 3, 6 / 5} by
            rw [this]
            repeat rw [Set.encard_insert_of_not_mem]
            simp
            norm_num
            simp
            norm_num
            simp
            norm_num
        ext x
        simp
        constructor
        .
            intro hx
            by_cases l: x < 0
            .
                rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
                by_cases l1: 2 * -x - 2 ^ 2 < 0
                .
                    rw [show |2 * -x - 2 ^ 2| = -(2 * -x - 2 ^ 2) by apply abs_of_nonpos; linarith] at hx
                    linarith
                .
                    rw [show |2 * -x - 2 ^ 2| = (2 * -x - 2 ^ 2) by apply abs_of_nonneg; linarith] at hx
                    left
                    nlinarith
            .
                rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
                by_cases l1: 2 * x - 2 ^ 2 < 0
                .
                    rw [show |2 * x - 2 ^ 2| = -(2 * x - 2 ^ 2) by apply abs_of_nonpos; linarith] at hx
                    right
                    right
                    linarith
                .
                    rw [show |2 * x - 2 ^ 2| = (2 * x - 2 ^ 2) by apply abs_of_nonneg; linarith] at hx
                    right
                    left
                    nlinarith
        .
            intro hx
            rcases hx with f | f | f
            all_goals simp [f]
            .
                ring
            .
                rw [show |(10: ℝ) / 3| = 10 / 3 by apply abs_of_nonneg; norm_num]
                norm_num
                rw [show |(8: ℝ) / 3| = 8 / 3 by apply abs_of_nonneg; norm_num]
                norm_num
            .
                rw [show |(6: ℝ) / 5| = 6 / 5 by apply abs_of_nonneg; norm_num]
                norm_num
                rw [show |(8: ℝ) / 5| = 8 / 5 by apply abs_of_nonneg; norm_num]
                norm_num



    -- case when a = -1/2
    .
        simp [h]
        suffices {x: ℝ | 2 * |2 * |x| - (-1 / 2) ^ 2| = x - -1 / 2} = {-1 / 5, 0, 1 / 3} by
            rw [this]
            repeat rw [Set.encard_insert_of_not_mem]
            simp
            norm_num
            simp
            norm_num
        ext x
        simp
        constructor
        .
            intro hx
            by_cases l: x < 0
            .
                rw [show |x| = -x by apply abs_of_nonpos; linarith] at hx
                by_cases l1: 2 * -x - (-1 / 2) ^ 2 < 0
                .
                    rw [show |2 * -x - (-1 / 2) ^ 2| = -(2 * -x - (-1 / 2) ^ 2) by apply abs_of_nonpos; linarith] at hx
                    linarith
                .
                    rw [show |2 * -x - (-1 / 2) ^ 2| = (2 * -x - (-1 / 2) ^ 2) by apply abs_of_nonneg; linarith] at hx
                    left
                    nlinarith
            .
                rw [show |x| = x by apply abs_of_nonneg; linarith] at hx
                by_cases l1: 2 * x - (-1 / 2) ^ 2 < 0
                .
                    rw [show |2 * x - (-1 / 2) ^ 2| = -(2 * x - (-1 / 2) ^ 2) by apply abs_of_nonpos; linarith] at hx
                    ring_nf at hx
                    right
                    left
                    nlinarith
                .
                    rw [show |2 * x - (-1 / 2) ^ 2| = (2 * x - (-1 / 2) ^ 2) by apply abs_of_nonneg; linarith] at hx
                    ring_nf at hx
                    right
                    right
                    nlinarith
        .
            intro hx
            rcases hx with f | f | f
            all_goals simp [f]; norm_num
            .
                rw [show |(1: ℝ) / 5| = 1 / 5 by apply abs_of_nonneg; norm_num]
                norm_num
                rw [show |(3: ℝ) / 20| = 3 / 20 by apply abs_of_nonneg; norm_num]
                norm_num
            .
                rw [show |(1: ℝ) / 3| = 1 / 3 by apply abs_of_nonneg; norm_num]
                norm_num
                rw [show |(5: ℝ) / 12| = 5 / 12 by apply abs_of_nonneg; norm_num]
                norm_num