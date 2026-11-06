import Mathlib

theorem number_theory_40873 (n : ℕ) (hn : n > 0) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ n = (Nat.lcm x y + Nat.lcm y z) / Nat.lcm x z ↔
    Even n := by
  by_cases h : Even n
  · -- Assume n is even
    have h1 : n % 2 = 0 := by
      obtain ⟨k, hk⟩ := h
      omega
    use 1
    use n / 2
    use 1
    constructor
    · -- Assume the left side is true, prove the right side
      intro h
      tauto
    · -- Assume the right side is true, prove the left side
      intro h
      constructor
      · norm_num
      constructor
      · -- Show positivity
        omega
      constructor
      · -- Show positivity
        omega
      · -- Show the equation holds
        have h2 : n % 2 = 0 := h1
        have h3 : 2 * (n / 2) = n := by
          omega
        simp [Nat.lcm, h3] at *
        all_goals
          omega
  · -- Assume n is odd
    have h1 : n % 2 = 1 := by
      by_contra h1
      push_neg at h1
      have : Even n := by
        refine' ⟨n / 2, by omega⟩
      tauto
    use 0
    use 0
    use 0
    simp [h1, Nat.even_iff] at *
    <;> try { tauto }