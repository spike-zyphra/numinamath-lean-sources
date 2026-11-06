import Mathlib

theorem number_theory_28828 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (h1 : m ^ 2 + n ^ 2 = 3789) (h2 : Nat.gcd m n + Nat.lcm m n = 633) :
    m + n = 87 := by
  have h3 : m ≤ 61 := by
    nlinarith
  have h4 : n ≤ 61 := by
    nlinarith
  interval_cases m <;> interval_cases n
    <;> norm_num [Nat.lcm] at h1 h2 ⊢
    <;> omega