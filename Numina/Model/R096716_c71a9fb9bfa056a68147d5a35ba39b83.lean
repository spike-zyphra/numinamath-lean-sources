import Mathlib

theorem number_theory_3796 (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (h1 : Nat.gcd m n = 12) (h2 : 3 * m + 5 * n = 336) :
    m + n = 72 := by
  have h3 : m ≤ 112 := by
    omega
  have h4 : n ≤ 67 := by
    omega
  interval_cases m <;> interval_cases n <;> norm_num at h1 h2 ⊢ <;> omega