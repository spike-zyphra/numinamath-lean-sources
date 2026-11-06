import Mathlib

theorem number_theory_241444 : IsLeast {k | ∃ n : ℕ, (2018 * 2019 * 2020 * 2021 + k) = n ^ 2} 1 := by 
  constructor
  · -- Verify that 1 belongs to the set
    use 2018^2 + 3 * 2018 + 1
    all_goals
      norm_num
  · -- Verify that 1 is indeed minimal
    intro k hk
    rcases hk with ⟨n, hn⟩
    by_contra h'
    push_neg at h'
    -- Assume k < 1, which means k = 0 for k ∈ ℕ
    have h0 : k = 0 := by
      omega
    rw [h0] at hn
    -- We need to prove that the equation 2018 * 2019 * 2020 * 2021 = n^2 is impossible
    have h1 : n ≤ 2018^2 + 3 * 2018 := by
      nlinarith
    have h2 : n < 2018^2 + 3 * 2018 + 1 := by
      nlinarith
    have h4 : n ^ 2 < (2018^2 + 3 * 2018 + 1) ^ 2 := by
      nlinarith
    have h6 : n ^ 2 > (2018^2 + 3 * 2018) ^ 2 := by
      nlinarith
    have h5 : n > 2018^2 + 3 * 2018 := by
      by_contra h
      push_neg at h
      have h7 : n ≤ 2018^2 + 3 * 2018 := by
        omega
      have h7' : n ^ 2 ≤ (2018^2 + 3 * 2018) ^ 2 := by
        nlinarith
      nlinarith
    nlinarith