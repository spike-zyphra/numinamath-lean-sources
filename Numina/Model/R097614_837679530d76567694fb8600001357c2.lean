import Mathlib

theorem number_theory_300294 (n : ℤ) (h : ¬ 5 ∣ n) : (n^4 + 4) % 5 = 0 := by
  have h1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    have h2 : n % 5 ≠ 0 := by
      by_contra h3
      have : 5 ∣ n := by
        omega
      contradiction
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- Case n % 5 = 1
    have h2 : n ^ 4 % 5 = 1 := by
      have h3 : n % 5 = 1 := h1
      have h4 : n ^ 4 % 5 = 1 := by
        have h5 : n % 5 = 1 := h3
        have h6 : n ^ 4 % 5 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h5]
          all_goals omega
        exact h6
      exact h4
    omega
  · -- Case n % 5 = 2
    have h2 : n ^ 4 % 5 = 1 := by
      have h3 : n % 5 = 2 := h1
      have h4 : n ^ 4 % 5 = 1 := by
        have h5 : n % 5 = 2 := h3
        have h6 : n ^ 4 % 5 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h5]
          all_goals omega
        exact h6
      exact h4
    omega
  · -- Case n % 5 = 3
    have h2 : n ^ 4 % 5 = 1 := by
      have h3 : n % 5 = 3 := h1
      have h4 : n ^ 4 % 5 = 1 := by
        have h5 : n % 5 = 3 := h3
        have h6 : n ^ 4 % 5 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h5]
          all_goals omega
        exact h6
      exact h4
    omega
  · -- Case n % 5 = 4
    have h2 : n ^ 4 % 5 = 1 := by
      have h3 : n % 5 = 4 := h1
      have h4 : n ^ 4 % 5 = 1 := by
        have h5 : n % 5 = 4 := h3
        have h6 : n ^ 4 % 5 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h5]
          all_goals omega
        exact h6
      exact h4
    omega