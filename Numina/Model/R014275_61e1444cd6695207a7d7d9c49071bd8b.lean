import Mathlib

theorem number_theory_241344 : IsLeast {k | ∃ n, 2019 * 2020 * 2021 * 2022 + k = n ^ 2} 1 := by 
  constructor
  · -- Show 1 is in the set.
    use 2019 * 2022 + 1
    all_goals norm_num
  · -- Show no smaller element is in the set.
    intro k hk
    rcases hk with ⟨n, hn⟩
    by_contra h
    push_neg at h
    have h0 : k = 0 := by 
      omega
    rw [h0] at hn
    have h1 : n ≤ 2019 * 2022 := by
      nlinarith [show n ^ 2 ≤ (2019 * 2020 * 2021 * 2022 : ℕ) from by nlinarith, 
          show 2019 * 2020 * 2021 * 2022 < (2019 * 2022 + 1) ^ 2 by norm_num]
    have h2 : n ≥ 2019 * 2022 := by
      nlinarith [show n ^ 2 ≥ (2019 * 2020 * 2021 * 2022 : ℕ) from by nlinarith, 
          show (2019 * 2022) ^ 2 < 2019 * 2020 * 2021 * 2022 + (2019 * 2022) by norm_num]
    have h3 : n = 2019 * 2022 := by 
      nlinarith
    rw [h3] at hn
    all_goals nlinarith