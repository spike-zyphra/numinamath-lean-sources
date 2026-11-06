import Mathlib

open BigOperators Real Set

theorem algebra_11972 {f : ℝ → ℝ}
  (hf : ∀ x, x > 1 → f x = log x)
  (hf' : ∀ x, x ≤ 1 → f x = 1/2 * x + 1/2)
  (m n : ℝ) (hm : m < n) (hmn : f m = f n) :
  n - m ≥ 3 - 2 * log 2 := by
  by_cases h1 : m ≤ 1
  · -- If m ≤ 1, then f(m) = m/2 + 1/2
    have hm2' : f m = 1/2 * m + 1/2 := hf' m (show m ≤ 1 by linarith)
    by_cases h3 : n > 1
    · -- If n > 1, then f(n) = log n
      have hn1 : f n = log n := hf n (show 1 < n by linarith)
      rw [hm2', hn1] at hmn
      have h2 : m = 2 * log n - 1 := by
        linarith
      have h3' : n - m ≥ 3 - 2 * log 2 := by
        rw [show m = 2 * log n - 1 by linarith [h2]]
        have h4 : n > 1 := by linarith
        have h5 : n - (2 * log n - 1) ≥ 3 - 2 * log 2 := by
          have h6 : (n) - 2 * log n ≥ 2 - 2 * log 2 := by
            have h7 : (n) - 2 * log n - (2 - 2 * log 2) ≥ 0 := by
              have h8 : (n) - 2 * log n - (2 - 2 * log 2) = (n - 2) - 2 * (log n - log 2) := by
                ring_nf
              rw [h8]
              have h13 : (n - 2) - 2 * (log n - log 2) ≥ 0 := by
                have h14 : (n - 2) - 2 * (log n - log 2) = (n - 2) - 2 * log (n / 2) := by
                  have h9 : log (n / 2) = log n - log 2 := by
                    rw [log_div (by linarith) (by norm_num)]
                  rw [h9]
                rw [h14]
                have h19 : (n - 2) - 2 * log (n / 2) ≥ 0 := by
                  have h7 : n > 1 := by linarith
                  have h21 : (n / 2) > 0 := by nlinarith
                  have h22 : log (n / 2) ≤ (n / 2) - 1 := by
                    have h23 : (n / 2) > 0 := by nlinarith
                    have h24 : log (n / 2) ≤ (n / 2) - 1 := by
                      linarith [Real.log_le_sub_one_of_pos (show 0 < n / 2 by linarith)]
                    linarith
                  nlinarith
                linarith
              linarith
            nlinarith
          nlinarith
        nlinarith
      linarith
    · -- If n ≤ 1, then f(n) = n/2 + 1/2
      have hn2' : f n = 1/2 * n + 1/2 := hf' n (show n ≤ 1 by linarith)
      rw [hm2', hn2'] at hmn
      have h_eq : m = n := by
        linarith
      linarith
  · -- If m > 1, then f(m) = log m
    have hm1 : f m = log m := hf m (show 1 < m by linarith)
    by_cases h3 : n > 1
    · -- If n > 1, then f(n) = log n
      have hn1 : f n = log n := hf n (show 1 < n by linarith)
      rw [hm1, hn1] at hmn
      have h_eq : m = n := by
        apply log_injOn_pos (Set.mem_Ioi.mpr (show 0 < m by linarith)) (Set.mem_Ioi.mpr (show 0 < n by linarith)) hmn
      linarith
    · -- If n ≤ 1, then f(n) = n/2 + 1/2
      have hn2' : f n = 1/2 * n + 1/2 := hf' n (show n ≤ 1 by linarith)
      rw [hm1, hn2'] at hmn
      have h7 : m > 1 := by linarith
      have h9 : n > 1 := by
        by_contra h
        push_neg at h
        have h10 : n ≤ 1 := by linarith
        have h11 : log m = 1/2 * n + 1/2 := by
          linarith
        have h12 : log m > 0 := by
          apply Real.log_pos
          linarith
        have h13 : (1/2 * n + 1/2) ≤ (1/2 : ℝ) := by
          nlinarith
        nlinarith
      linarith