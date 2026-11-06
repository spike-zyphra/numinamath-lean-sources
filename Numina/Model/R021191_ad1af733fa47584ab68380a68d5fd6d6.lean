import Mathlib

theorem number_theory_241247 :
    IsLeast {k | ∃ m : ℕ, m^2 = 2017 * 2018 * 2019 * 2020 + k} 1 := by
  constructor
  · -- Show 1 is in the set
    use 2017 ^ 2 + 3 * 2017 + 1
    all_goals
      norm_num
  · -- Show that 1 is the minimum
    intro k hk
    rcases hk with ⟨m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k = 0 := by
      omega
    rw [h1] at hm
    -- Note that m^2 = 2017 * 2018 * 2019 * 2020
    -- The right-hand side is not a perfect square
    -- However Lean can detect automatically this
    -- impossible equation
    have h2 : m ≤ 2017 * 2020 := by
      nlinarith
    have h3 : m ≥ 2017 * 2020 := by
      nlinarith
    nlinarith