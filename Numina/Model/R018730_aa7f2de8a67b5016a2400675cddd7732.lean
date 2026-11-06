import Mathlib

theorem number_theory_294595 (m n p : ℕ) (hm : m.Prime) (hn : n.Prime) (hp : p.Prime)
    (hmn : m > n) (hmp : m > p) (hnp : n > p) (hsum : m + n + p = 74) (hdiff : m - n - p = 44) :
    m = 59 ∧ n = 13 ∧ p = 2 := by

  have eq1 : m = 59 := by
    omega

  -- Substitute m into the sum to get n + p
  have eq2 : n + p = 15 := by
    omega

  -- Now, given that n and p are primes with n + p = 15 and n > p
  have eq3 : n = 13 := by
    have h1 : n ≤ 15 := by
      omega

    have hp1 : p ≤ 15 := by
      omega

    interval_cases n <;> interval_cases p
      <;> norm_num at hn hp eq2
      <;> omega

  -- From n = 13 and n + p = 15 we get p = 2
  have eq4 : p = 2 := by
    omega

  -- Therefore, we can conclude everything
  constructor
  · exact eq1
  constructor
  · exact eq3
  · exact eq4