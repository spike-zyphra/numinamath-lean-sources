import Mathlib

theorem inequalities_46408 (k : ℤ) :
    (∀ m n : ℤ, m > 0 → n > 0 → m^3 + n^3 > (m + n)^2 → m^3 + n^3 ≥ (m + n)^2 + k) ↔
    k ≤ 10 := by
  constructor
  · -- Assume the inequality holds for all positive integers m, n
    intro h
    have h1 := h 2 3 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1 
    linarith
  · -- Show that if k ≤ 10, then the inequality holds
    intro hk m n hm hn h
    have h1 : m^3 + n^3 ≥ (m + n)^2 + k := by
      have h2 : m^3 + n^3 - (m + n) ^ 2 ≥ 10 := by
        by_contra h
        push_neg at h
        have h3 : m ≤ 5 := by
          nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 2 : ℤ), 
            sq_nonneg (m^2 - n^2 : ℤ), sq_nonneg (m * n : ℤ), 
              sq_nonneg ((m + n) : ℤ), h, sq_nonneg ((m - n) * (m + n) : ℤ)]
        have h4 : n ≤ 5 := by
          nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 2 : ℤ), 
            sq_nonneg (m^2 - n^2 : ℤ), sq_nonneg (m * n : ℤ), 
              sq_nonneg ((m + n) : ℤ), h, sq_nonneg ((m - n) * (m + n) : ℤ)]
        interval_cases m <;> interval_cases n <;> omega
      linarith 
    linarith