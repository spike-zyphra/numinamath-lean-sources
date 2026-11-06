import Mathlib

theorem algebra_231121 (m n : ℤ) : m^3 + n^3 = (m + n)^2 ↔
    (m = -n ∨ (m = 0 ∧ n = 1) ∨ (m = 1 ∧ n = 0) ∨ (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 2 ∧ n = 2)) := by
  constructor
  · -- Forward direction: if the equation holds, then one of the cases must also hold
    intro h_eq
    have h1 : m^3 + n^3 = (m + n) ^ 2 := by linarith
    by_cases h : m = -n
    · -- m = -n
      simp [h]
      all_goals omega
    · -- m ≠ -n
      have h1a : m^3 + n^3 = (m + n) ^ 2 := by linarith
      have h2a : m + n ≠ 0 := by
        intro h_eq_zero
        apply h
        omega
      -- Given $m ≠ -n, $ then $m + n ≠ 0$

      -- Use arithmetices to find all integer-m,n satisfy the equation
      have h3a : m^2 - m * n + n^2 = m + n := by
        have h4a : m + n ≠ 0 := h2a
        have eq1 : m ^ 3 + n ^ 3 = (m + n) * (m ^ 2 - m * n + n ^ 2) := by ring
        have eq2 : m ^ 3 + n ^ 3 = (m + n) ^ 2 := h1a
        have eq3 : (m + n) * (m ^ 2 - m * n + n ^ 2) = (m + n) ^ 2 := by 
          linarith [eq1, eq2]
        have h5a : m^2 - m * n + n^2 = m + n := by
          apply (mul_left_inj' h4a).mp
          linarith
        linarith
      -- Find the bounds of integer m, n 
      have h4a : m ≤ 4 := by 
        nlinarith [sq_nonneg (m - n), sq_nonneg (m + n - 2), sq_nonneg (m - 2), sq_nonneg (n - 2)]
      have h5a : m ≥ -4 := by 
        nlinarith [sq_nonneg (m - n), sq_nonneg (m + n - 2), sq_nonneg (m - 2), sq_nonneg (n - 2)]
      have h6a : n ≤ 4 := by 
        nlinarith [sq_nonneg (m - n), sq_nonneg (m + n - 2), sq_nonneg (m - 2), sq_nonneg (n - 2)]
      have h7a : n ≥ -4 := by 
        nlinarith [sq_nonneg (m - n), sq_nonneg (m + n - 2), sq_nonneg (m - 2), sq_nonneg (n - 2)]
      interval_cases m <;> interval_cases n <;> omega
  · -- Backward direction: if one of the cases holds, then the equation is also true
    rintro (h | h | h | h | h | h)
    · -- m = -n 
      rw [show n = -m from by linarith [h]]
      ring_nf
    · -- m = 0 ∧ n = 1 
      rcases h with ⟨h1, h2⟩
      rw [h1, h2]
      norm_num 
    · -- m = 1 ∧ n = 0 
      rcases h with ⟨h1, h2⟩
      rw [h1, h2]
      norm_num 
    · -- m = 1 ∧ n = 2 
      rcases h with ⟨h1, h2⟩
      rw [h1, h2]
      norm_num 
    · -- m = 2 ∧ n = 1 
      rcases h with ⟨h1, h2⟩
      rw [h1, h2]
      norm_num
    · -- m = 2 ∧ n = 2 
      rcases h with ⟨h1, h2⟩
      rw [h1, h2]
      norm_num