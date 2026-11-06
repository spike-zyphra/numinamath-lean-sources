import Mathlib

open Finset Real Nat

/-The sum of the first thirteen terms of a certain arithmetic progression is 50% of the sum of the last thirteen terms of this progression. The sum of all terms of this progression except the first three is to the sum of all terms except the last three as
4:3. Find the number of terms in this progression.-/

theorem algebra_240838 (n : ℕ) (hn : n ≥ 13) (a : ℕ → ℝ) (h : ∃ d, d ≠ 0 ∧ ∀ k: ℕ, a k = a 0 + d * k)
    (h1 : ∑ i ∈ Icc 0 12, a i = 50 / 100 * ∑ i ∈ Icc (n - 13) (n - 1), a i)
    (h2 : ∑ i ∈ Icc 3 (n - 1), a i = 4 / 3 * ∑ i ∈ Icc 0 (n - 4), a i) :
    n = 20 := by

    obtain ⟨d, hd, h⟩ := h

    -- we first compute all the sums using induction
    have eq: ∀ p q, p ≤ q → ∑ i ∈ Icc p q, a i = (a 0 + d * (p + q) / 2) * (q - p + 1) := by
        intro p q l
        induction' q with q ih
        -- base case
        .
            replace l: p = 0 := by omega
            simp [l]
        .
            by_cases s: p = q + 1
            .
                rw [← s]
                simp
                specialize h p
                rw [h]
                field_simp
                ring
            .
                replace l: p ≤ q := by
                    omega
                clear s
                simp [l] at ih
                rw [Finset.sum_Icc_succ_top]
                rw [ih]
                specialize h (q + 1)
                rw [h]
                field_simp
                ring
                omega

    -- then we use eq to simplify h1 and h2
    have eq1:= eq 0 12 (by norm_num)
    norm_num at eq1
    rw [eq1] at h1
    clear eq1

    have eq2:= eq (n - 13) (n - 1) (by omega)
    norm_num at eq2
    rw [eq2] at h1
    clear eq2

    have eq3:= eq 3 (n - 1) (by omega)
    norm_num at eq3
    rw [eq3] at h2
    clear eq3

    have eq4:= eq 0 (n - 4) (by omega)
    norm_num at eq4
    rw [eq4] at h2
    clear eq4

    -- finally, we can compute the value of n
    clear eq h
    rw [show (50: ℝ) / 100 = 1 / 2 by norm_num] at h1
    field_simp at h1 h2
    rify
    replace h1: a 0 = d * (↑n - 19) := by nlinarith
    have s: ↑(n - 4) = n - (4: ℝ) := by
        apply Nat.cast_sub
        omega
    rw [s] at h2
    replace h2: 2 * a 0 = (22 - n) * d := by nlinarith
    rw [h1] at h2
    replace h2: d * (3 * n - 60) = 0 := by nlinarith
    simp [hd] at h2
    linarith