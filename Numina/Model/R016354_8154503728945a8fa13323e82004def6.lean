import Mathlib

theorem number_theory_110242 :
    IsGreatest {n | n % 91 = (n / 91)^2} 900 := by
  constructor
  · -- Show 900 in the set.
    show 900 % 91 = (900 / 91) ^ 2
    norm_num
  · -- Show that if n in the set, then n ≤ 900.
    intro n hn
    have h1 : n % 91 = (n / 91) ^ 2 := hn
    by_contra h
    push_neg at h
    have h2 : n % 91 < 91 := by
      omega
    have h4 : (n / 91 : ℕ) ≤ 9 := by
      nlinarith [h1, h2]
    -- Now use q <= 9 to show n <= 900.
    have h5 : n ≤ 900 := by
      have h6 : n % 91 = (n / 91) ^ 2 := h1
      have h8 : (n / 91 : ℕ) ≤ 9 := h4
      have h7 : n = 91 * (n / 91) + (n % 91) := by
        omega
      rw [h6] at h7
      nlinarith [sq_nonneg ((n / 91 : ℕ) : ℕ), sq_nonneg ((n / 91 : ℕ) - 9 : ℤ)]
    linarith