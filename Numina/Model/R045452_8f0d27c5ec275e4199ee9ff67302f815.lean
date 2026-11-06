import Mathlib

open Real

theorem algebra_11746 : IsLeast {n > 0 | ∑ k ∈ Finset.Icc 0 n, logb 2 (1 + 1 / 2^(2^k)) ≥ 1 + logb 2 (2014 / 2015) } 3 := by
  constructor
  · -- Show 3 is in the set
    constructor
    · -- Show 3 > 0
      norm_num
    · -- Show that the inequality holds for n = 3
      have h2 : ∑ k in Finset.Icc (0 : ℕ) 3, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) = logb 2 (65535 / 32768 : ℝ) := by
        have h3 : ∑ k in Finset.Icc (0 : ℕ) 3, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) =
            logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) + logb 2 (17 / 16 : ℝ) + logb 2 (257 / 256 : ℝ) := by
            -- Compute the sum directly
            norm_num [Finset.sum_Icc_succ_top, Finset.sum_singleton]
            <;> try { native_decide } <;> try { native_decide }
        have h4 : logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) + logb 2 (17 / 16 : ℝ) + logb 2 (257 / 256 : ℝ) =
            logb 2 ((3 / 2 : ℝ) * (5 / 4 : ℝ) * (17 / 16 : ℝ) * (257 / 256 : ℝ)) := by
            rw [← logb_mul (by norm_num) (by norm_num), ← logb_mul (by norm_num) (by norm_num), ← logb_mul (by norm_num) (by norm_num)]
            all_goals try { norm_num }
            all_goals try { native_decide }
        have h5 : (3 / 2 : ℝ) * (5 / 4 : ℝ) * (17 / 16 : ℝ) * (257 / 256 : ℝ) = (65535 / 32768 : ℝ) := by norm_num
        rw [h3, h4, h5]
        all_goals try { native_decide }
      have h1 : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (4028 / 2015 : ℝ) := by
        have h2 : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) := by
          have h3 : logb 2 (2 : ℝ) = (1 : ℝ) := by
            rw [logb_eq_iff_rpow_eq] <;> norm_num
          linarith [h3]
        rw [h2]
        have h4 : (2 : ℝ) * (2014 / 2015 : ℝ) = (4028 / 2015 : ℝ) := by
          norm_num
        have h5 : logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 ((2 : ℝ) * (2014 / 2015 : ℝ)) := by
          rw [← logb_mul (by norm_num) (by norm_num)]
        rw [h5, h4]
        all_goals try { native_decide }
      rw [h2, h1]
      have h3 : logb (2 : ℝ) (65535 / 32768 : ℝ) ≥ logb (2 : ℝ) (4028 / 2015 : ℝ) := by
        have h4 : (65535 / 32768 : ℝ) ≥ (4028 / 2015 : ℝ) := by norm_num
        have h5 : logb (2 : ℝ) ((65535 / 32768 : ℝ)) ≥ logb (2 : ℝ) ((4028 / 2015 : ℝ)) := by
          apply Real.logb_le_logb_of_le
          all_goals try { norm_num }
          all_goals try { native_decide }
        linarith
      linarith
      all_goals try norm_num
  · -- Show that no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_ineq⟩
    by_contra h
    push_neg at h
    have h1 : n = 1 ∨ n = 2 := by
      have h2 : n > 0 := hn_pos
      have h3 : n < 3 := by linarith
      omega
    rcases h1 with (rfl | rfl)
    · -- Case n = 1
      have h2 : ∑ k in Finset.Icc (0 : ℕ) 1, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) = logb 2 (15 / 8 : ℝ) := by
        have h3 : ∑ k in Finset.Icc (0 : ℕ) 1, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) =
            logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) := by
            -- Compute the sum directly
            norm_num [Finset.sum_Icc_succ_top, Finset.sum_singleton]
            <;> try { native_decide } <;> try { native_decide }
        have h6 : logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) = logb 2 ((3 / 2 : ℝ) * (5 / 4 : ℝ)) := by
          rw [← logb_mul (by norm_num) (by norm_num)]
        have h7 : (3 / 2 : ℝ) * (5 / 4 : ℝ) = (15 / 8 : ℝ) := by norm_num
        rw [h3, h6, h7]
        all_goals try { native_decide }
      have h11 : logb (2 : ℝ) (15 / 8 : ℝ) < logb (2 : ℝ) (4028 / 2015 : ℝ) := by
        have h13 : (15 / 8 : ℝ) < (4028 / 2015 : ℝ) := by norm_num
        have h14 : logb (2 : ℝ) (15 / 8 : ℝ) < logb (2 : ℝ) (4028 / 2015 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals linarith
          all_goals linarith
        linarith
      have h12 : ∑ k in Finset.Icc (0 : ℕ) 1, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) ≥ (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) := by
        linarith [hn_ineq]
      have h1' : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (4028 / 2015 : ℝ) := by
        have h2 : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) := by
          have h3 : logb 2 (2 : ℝ) = (1 : ℝ) := by
            rw [logb_eq_iff_rpow_eq] <;> norm_num
          linarith [h3]
        rw [h2]
        have h4 : (2 : ℝ) * (2014 / 2015 : ℝ) = (4028 / 2015 : ℝ) := by
          norm_num
        have h5 : logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 ((2 : ℝ) * (2014 / 2015 : ℝ)) := by
          rw [← logb_mul (by norm_num) (by norm_num)]
        rw [h5, h4]
        all_goals try { native_decide }
      linarith [h1', h2, h11, hn_ineq]
      all_goals try norm_num
    · -- Case n = 2
      have h2 : ∑ k in Finset.Icc (0 : ℕ) 2, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) = logb 2 (255 / 128 : ℝ) := by
        have h3 : ∑ k in Finset.Icc (0 : ℕ) 2, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) =
            logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) + logb 2 (17 / 16 : ℝ) := by
            -- Compute the sum directly
            norm_num [Finset.sum_Icc_succ_top, Finset.sum_singleton]
            <;> try { native_decide } <;> try { native_decide }
        have h6 : logb 2 (3 / 2 : ℝ) + logb 2 (5 / 4 : ℝ) + logb 2 (17 / 16 : ℝ) = logb 2 ((3 / 2 : ℝ) * (5 / 4 : ℝ) * (17 / 16 : ℝ)) := by
            rw [← logb_mul (by norm_num) (by norm_num), ← logb_mul (by norm_num) (by norm_num)]
            all_goals try { norm_num }
            all_goals try { native_decide }
        have h7 : (3 / 2 : ℝ) * (5 / 4 : ℝ) * (17 / 16 : ℝ) = (255 / 128 : ℝ) := by norm_num
        rw [h3, h6, h7]
        all_goals try { native_decide }
      have h11 : logb (2 : ℝ) (255 / 128 : ℝ) < logb (2 : ℝ) (4028 / 2015 : ℝ) := by
        have h13 : (255 / 128 : ℝ) < (4028 / 2015 : ℝ) := by norm_num
        have h14 : logb (2 : ℝ) (255 / 128 : ℝ) < logb (2 : ℝ) (4028 / 2015 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals linarith
          all_goals linarith
        linarith
      have h12 : ∑ k in Finset.Icc (0 : ℕ) 2, logb 2 (1 + 1 / 2 ^ (2 ^ k) : ℝ) ≥ (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) := by
        linarith [hn_ineq]
      have h1' : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (4028 / 2015 : ℝ) := by
        have h2 : (1 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) := by
          have h3 : logb 2 (2 : ℝ) = (1 : ℝ) := by
            rw [logb_eq_iff_rpow_eq] <;> norm_num
          linarith [h3]
        rw [h2]
        have h4 : (2 : ℝ) * (2014 / 2015 : ℝ) = (4028 / 2015 : ℝ) := by
          norm_num
        have h5 : logb 2 (2 : ℝ) + logb 2 (2014 / 2015 : ℝ) = logb 2 ((2 : ℝ) * (2014 / 2015 : ℝ)) := by
          rw [← logb_mul (by norm_num) (by norm_num)]
        rw [h5, h4]
        all_goals try { native_decide }
      linarith [h1', h2, h11, hn_ineq]
      all_goals try norm_num