import Mathlib

/- Let the real numbers $a, b, c, d, e$ be such that $|a-b|=|b-c|=|c-d|=|d-e|=|e-a|$. Prove that $a=b=c=d=e$.

Gazeta Matematică - nr.10/ 2012 -/

theorem algebra_99587 {a b c d e : ℝ} (h1 : abs (a - b) = abs (b - c)) (h2 : abs (b - c) = abs (c - d))
    (h3 : abs (c - d) = abs (d - e)) (h4 : abs (d - e) = abs (e - a)):
    a = b ∧ b = c ∧ c = d ∧ d = e := by

    set k:= |a - b| with hk  -- it suffices to show that k is zero

    -- we first express the abs in term of k
    replace h1: |b - c| = k := by linarith
    replace h2: |c - d| = k := by linarith
    replace h3: |d - e| = k := by linarith
    replace h4: |e - a| = k := by linarith

    -- then we show that k = 0
    have o: k = 0 := by
        
        -- firstly we take out the abs sign
        replace hk: a - b = k ∨ a - b = - k := by
            by_cases l: a ≤ b
            .
                rw [show |a - b| = - (a - b) by apply abs_of_nonpos; linarith] at hk
                right
                linarith
            .
                rw [show |a - b| = (a - b) by apply abs_of_nonneg; linarith] at hk
                left
                linarith
        replace h1: b - c = k ∨ b - c = - k := by
            by_cases l: b ≤ c
            .
                rw [show |b - c| = - (b - c) by apply abs_of_nonpos; linarith] at h1
                right
                linarith
            .
                rw [show |b - c| = (b - c) by apply abs_of_nonneg; linarith] at h1
                left
                linarith
        replace h2: c - d = k ∨ c - d = - k := by
            by_cases l: c ≤ d
            .
                rw [show |c - d| = - (c - d) by apply abs_of_nonpos; linarith] at h2
                right
                linarith
            .
                rw [show |c - d| = (c - d) by apply abs_of_nonneg; linarith] at h2
                left
                linarith
        replace h3: d - e = k ∨ d - e = - k := by
            by_cases l: d ≤ e
            .
                rw [show |d - e| = - (d - e) by apply abs_of_nonpos; linarith] at h3
                right
                linarith
            .
                rw [show |d - e| = (d - e) by apply abs_of_nonneg; linarith] at h3
                left
                linarith
        replace h4: e - a = k ∨ e - a = - k := by
            by_cases l: e ≤ a
            .
                rw [show |e - a| = - (e - a) by apply abs_of_nonpos; linarith] at h4
                right
                linarith
            .
                rw [show |e - a| = (e - a) by apply abs_of_nonneg; linarith] at h4
                left
                linarith

        -- then we use the fact the sum of the terms are zero
        have s: (a - b) + (b - c) + (c - d) + (d - e) + (e - a) = 0 := by linarith

        -- then we show by enumating
        rcases hk with hk | hk  
        <;> rcases h1 with h1 | h1
        <;> rcases h2 with h2 | h2
        <;> rcases h3 with h3 | h3
        <;> rcases h4 with h4 | h4
        <;> simp [hk,h1,h2,h3,h4] at s
        all_goals ring_nf at s; try simp at s
        all_goals linarith

     -- finally take out the abs sign
    simp [o] at *

    by_cases l: a ≤ b
    .
        rw [show |a - b| = - (a - b) by apply abs_of_nonpos; linarith] at hk
        constructor
        .
            linarith
        .
            constructor
            .
                linarith
            .
                constructor
                .
                    linarith
                .
                    linarith

    .
        rw [show |a - b| = (a - b) by apply abs_of_nonneg; linarith] at hk
        constructor
        .
            linarith
        .
            constructor
            .
                linarith
            .
                constructor
                .
                    linarith
                .
                    linarith