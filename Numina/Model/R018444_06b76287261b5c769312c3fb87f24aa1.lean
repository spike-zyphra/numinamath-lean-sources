import Mathlib

theorem number_theory_205809 :
    IsLeast {n | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ m p q : ℕ, m^2 = a + b ∧ p^2 = b + c ∧ q^2 = c + a ∧ n = a + b + c} 55 := by
  constructor
  · -- Show 55 is in the set.
    use 19, 6, 30
    constructor
    · norm_num  -- a > 0
    constructor
    · norm_num  -- b > 0
    constructor
    · norm_num  -- c > 0
    constructor
    · norm_num  -- a ≠ b
    constructor
    · norm_num  -- a ≠ c
    constructor
    · norm_num  -- b ≠ c
    use 5, 6, 7
    all_goals norm_num
  · -- Show 55 is minimal in the set
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, hab1, hab2, hab3, m, p, q, hm, hp, hq, hn⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 55 := by
      linarith
    have h2 : m ≤ 7 := by
      nlinarith
    have h3 : p ≤ 7 := by
      nlinarith
    have h4 : q ≤ 7 := by
      nlinarith
    interval_cases m <;> interval_cases p <;> interval_cases q
      <;> omega