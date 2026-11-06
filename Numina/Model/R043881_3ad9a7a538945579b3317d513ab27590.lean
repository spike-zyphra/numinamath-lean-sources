import Mathlib

theorem number_theory_169773 (z : ℕ) :
    z ∈ {n | n ∈ Finset.Icc 100 999 ∧ ∃ p, Nat.Prime p ∧ n = 2 * p ∧
      (n / 10) % 10 = (n / 100) + 1 ∧ (n % 10) = 2 * (n / 100)} ↔
    z = 122 ∨ z = 346 ∨ z = 458 := by
  constructor
  · -- First direction: if z satisfies all conditions, then it's one of the three numbers.
    intro h
    rcases h with ⟨hz1, ⟨p, hp, hz2, h1, h2⟩⟩
    rw [Finset.mem_Icc] at hz1
    rcases hz1 with ⟨hz1l, hz1u⟩
    have h3 : z ≤ 999 := by linarith
    have h4 : z ≥ 100 := by linarith
    interval_cases z <;> norm_num at h1 h2 hz2 <;> 
      try { 
        have : p ≤ 499 := by 
          omega 
        interval_cases p <;> norm_num at hp hz2 <;> tauto 
      }
  · -- Backward implication: the three numbers satisfy all conditions.
    rintro (h | h | h)
    · -- z = 122 
      rw [h]
      constructor
      · -- Show that 122 is in the range [100, 999]
        norm_num [Finset.mem_Icc]
      · -- Show the existence of a prime p.
        use 61
        all_goals norm_num
    · -- z = 346 
      rw [h]
      constructor
      · -- Show that 346 is in the range [100, 999]
        norm_num [Finset.mem_Icc]
      · -- Show the existence of a prime p.
        use 173
        all_goals norm_num
    · -- z = 458 
      rw [h]
      constructor
      · -- Show that 458 is in the range [100, 999]
        norm_num [Finset.mem_Icc]
      · -- Show the existence of a prime p.
        use 229
        all_goals norm_num