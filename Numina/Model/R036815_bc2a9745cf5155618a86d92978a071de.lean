import Mathlib

open BigOperators Real Set

theorem calculus_224583 {f : ℝ → ℝ} (hf : ∀ x, x > 1 → f x = log x) (hf' : ∀ x, x ≤ 1 → f x = (1/2)*x + (1/2)) :
    IsLeast {x | ∃ m n, m < n ∧ f m = f n ∧ x = n - m} (3 - 2 * log 2) := by
  constructor
  · -- Show 3 - 2 * log 2 is in the set
    use 2 * log 2 - 1, 2
    constructor
    · -- Show m < n
      have h1 : log 2 > 0 := by
        apply log_pos
        all_goals
          linarith
      nlinarith [show log 2 < 1 by
        linarith [Real.log_two_lt_d9]
      ]
    constructor
    · -- Show f (2 * log 2 - 1) = f 2
      have hm : (2 * log 2 - 1 : ℝ) ≤ 1 := by
        have h3 : log 2 ≤ 1 := by
          have h4 : log 2 ≤ (1 : ℝ) := by
            linarith [Real.log_two_lt_d9]
          linarith
        nlinarith
      have h3 : f (2 * log 2 - 1) = (1 / 2) * (2 * log 2 - 1) + (1 / 2) := by
        apply hf' (2 * log 2 - 1)
        linarith [hm]
      have h4 : f 2 = log 2 := by
        apply hf 2
        all_goals
        norm_num
      rw [h3, h4]
      have h5 : (1 / 2) * (2 * log 2 - 1) + (1 / 2) = log 2 := by
        nlinarith
      linarith [h5]
    · -- Show 3 - 2 * log 2 = 2 - (2 * log 2 - 1)
      nlinarith
  · -- Show 3 - 2 * log 2 is the minimum
    intro x hx
    rcases hx with ⟨m, n, h1, h2, hx⟩
    have h3 : m ≤ 1 := by
      by_contra h
      push_neg at h
      have h4 : m > 1 := by linarith
      have h5 : n > 1 := by linarith
      have h6 : f m = log m := by
        apply hf m
        linarith
      have h7 : f n = log n := by
        apply hf n
        linarith
      rw [h6, h7] at h2
      have h8 : m = n := by
        exact log_injOn_pos (Set.mem_Ioi.mpr (show 0 < m by linarith)) (Set.mem_Ioi.mpr (show 0 < n by linarith)) h2
      linarith
    have h4 : n > 1 := by
      by_contra h
      push_neg at h
      have h5 : n ≤ 1 := by linarith
      have h6 : f m = (1 / 2) * m + (1 / 2) := by
        apply hf' m
        linarith
      have h7 : f n = (1 / 2) * n + (1 / 2) := by
        apply hf' n
        linarith
      rw [h6, h7] at h2
      nlinarith
    have h5 : f m = (1 / 2) * m + (1 / 2) := by
      apply hf' m
      linarith
    have h6 : f n = log n := by
      apply hf n
      linarith
    rw [h5, h6] at h2
    have h7 : m + 1 = 2 * log n := by
      nlinarith
    have h8 : n - m ≥ 3 - 2 * log 2 := by
      have h9 : m = 2 * log n - 1 := by
        linarith
      rw [h9]
      have h14 : n > 1 := by linarith
      have h16 : (n) - (2 * log n - 1) ≥ 3 - 2 * log 2 := by
        have h17 : (n) - (2 * log n - 1) = n - 2 * log n + 1 := by ring
        rw [h17]
        have h18 : n - 2 * log n + 1 ≥ 3 - 2 * log 2 := by
          have h19 : (n) - 2 * log n + 1 ≥ 3 - 2 * log 2 := by
            have h20 : n > 1 := by linarith
            have h21 : (n) - 2 * log n + 1 - (3 - 2 * log 2) ≥ 0 := by
              have h22 : (n) - 2 * log n + 1 - (3 - 2 * log 2) = (n - 2) - 2 * (log n - log 2) := by
                linarith
              rw [h22]
              have h40 : (n - 2) - 2 * (log n - log 2) ≥ 0 := by
                have h41 : log n - log 2 = log (n / 2) := by
                  rw [← Real.log_div (by linarith) (by linarith)]
                rw [h41]
                have h100 : (n - 2) - 2 * (log (n / 2)) ≥ 0 := by
                  have h101 : (n / 2) > 0 := by linarith
                  have h120 : (n - 2) - 2 * (log (n / 2)) ≥ 0 := by
                    have h121 : Real.log (n / 2) ≤ (n / 2 - 1) := by
                      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 2 by linarith)]
                    nlinarith
                  linarith
                linarith
              linarith
            nlinarith
          linarith
        linarith
      linarith
    have h27 : x ≥ 3 - 2 * log 2 := by
      have h28 : x = n - m := by
        linarith [hx]
      linarith [h28, h8]
    linarith