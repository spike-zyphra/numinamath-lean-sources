import Mathlib

theorem number_theory_97996 (n m : ℤ) (h : Even (n ^ 2 + m ^ 2)) :
    ¬(Odd (n + m)) := by
  by_contra h1
  obtain ⟨k, hk⟩ := h1
  have h2 : (n ^ 2 + m ^ 2) % 2 = 1 := by
    have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have h4 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · rcases h4 with (h4 | h4)
      · -- n even, m even: contradiction
        exfalso
        omega
      · -- n even, m odd: sum is odd
        have h5 : n ^ 2 % 2 = 0 := by
          simp [Int.pow_succ, Int.mul_emod, h3]
        have h6 : m ^ 2 % 2 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h4]
        omega
    · rcases h4 with (h4 | h4)
      · -- n odd, m even: sum is odd
        have h5 : n ^ 2 % 2 = 1 := by
          simp [Int.pow_succ, Int.mul_emod, h3]
        have h6 : m ^ 2 % 2 = 0 := by
          simp [Int.pow_succ, Int.mul_emod, h4]
        omega
      · -- n odd, m odd: contradiction
        exfalso
        omega
  obtain ⟨k, hk⟩ := h
  have h3 : (n ^ 2 + m ^ 2) % 2 = 0 := by
    omega
  omega