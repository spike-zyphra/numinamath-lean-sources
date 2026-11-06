import Mathlib

theorem number_theory_90375 {p q : ℕ → ℕ}
    (hp1 : p 1 = 1) (hq1 : q 1 = 1)
    (hpn : ∀ n, p (n + 1) = 2 * (q n)^2 - (p n)^2)
    (hqm : ∀ n, q (n + 1) = 2 * (q n)^2 + (p n)^2) :
    ∀ m n, Nat.Coprime (p m) (q n) := by
  -- Let's consider the base cases by applying recurrence at n=0
  have h1 := hpn 0
  have h2 := hqm 0
  -- Given base cases
  have h3 : p 1 = 1 := hp1
  have h4 : q 1 = 1 := hq1
  -- Substitute the values of p 1 and q 1 into the equations
  norm_num [h3, h4] at h1 h2
  all_goals
    omega