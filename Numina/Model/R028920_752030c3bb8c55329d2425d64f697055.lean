import Mathlib



theorem algebra_21249 :
    IsLeast {p | p.Prime ∧ p ∈ Finset.Icc 10 99 ∧ ∃ x y z, p = x^3 + y^3 + z^3} 17 := by
  constructor
  · -- Show that 17 belongs to the set.
    constructor
    · -- Verify that 17 is prime.
      norm_num
    constructor
    · -- Verify that 17 is a two-digit number.
      native_decide
    · -- Verify that 17 can be expressed as the sum of three positive cubes.
      use 1, 2, 2
      all_goals norm_num
  · -- Show that 17 is the smallest.
    intro p hp
    rcases hp with ⟨h_prime, hp2, ⟨x, y, z, heq⟩⟩
    rw [Finset.mem_Icc] at hp2
    by_contra h
    push_neg at h
    have h1 : p ≥ 10 := hp2.1
    have h2 : p ≤ 99 := hp2.2
    have h3 : p < 17 := by nlinarith
    have h4 : x ≤ 3 := by
      by_contra h
      push_neg at h
      have : x ^ 3 ≥ 64 := by
        have : x ≥ 4 := by linarith
        have h5 : x ^ 3 ≥ 4 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h5 ⊢
        linarith
      have h11 : x ^ 3 + y ^ 3 + z ^ 3 ≥ 64 := by linarith [show y ^ 3 ≥ 0 by positivity, show z ^ 3 ≥ 0 by positivity, this]
      have : p ≥ 64 := by linarith [heq, h11]
      linarith
    have h5 : y ≤ 3 := by
      by_contra h
      push_neg at h
      have : y ^ 3 ≥ 64 := by
        have : y ≥ 4 := by linarith
        have h5 : y ^ 3 ≥ 4 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h5 ⊢
        linarith
      have h11 : x ^ 3 + y ^ 3 + z ^ 3 ≥ 64 := by linarith [show x ^ 3 ≥ 0 by positivity, show z ^ 3 ≥ 0 by positivity, this]
      have : p ≥ 64 := by linarith [heq, h11]
      linarith
    have h6 : z ≤ 3 := by
      by_contra h
      push_neg at h
      have : z ^ 3 ≥ 64 := by
        have : z ≥ 4 := by linarith
        have h5 : z ^ 3 ≥ 4 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h5 ⊢
        linarith
      have h11 : x ^ 3 + y ^ 3 + z ^ 3 ≥ 64 := by linarith [show x ^ 3 ≥ 0 by positivity, show y ^ 3 ≥ 0 by positivity, this]
      have : p ≥ 64 := by linarith [heq, h11]
      linarith
    have h7 : p = 11 ∨ p = 13 := by 
      interval_cases p <;> norm_num at *
    rcases h7 with (h_eq | h_eq)
    · -- Case p = 11
      rw [h_eq] at heq
      interval_cases x <;> interval_cases y <;> interval_cases z 
      <;> omega
    · -- Case p = 13
      rw [h_eq] at heq
      interval_cases x <;> interval_cases y <;> interval_cases z 
      <;> omega