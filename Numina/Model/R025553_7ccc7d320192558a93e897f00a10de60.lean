import Mathlib

theorem number_theory_56092 :
    {x | ∃ n, x = n^2 ∧ (x = 11^2 + 13^2 + 17^2 ∨ x = 24^2 + 25^2 + 26^2 ∨
      x = 12^2 + 24^2 + 36^2 ∨ x = 11^2 + 12^2 + 132^2)}.encard = 1 := by 
  have h1 : {x | ∃ n, x = n^2 ∧ (x = 11^2 + 13^2 + 17^2 ∨ x = 24^2 + 25^2 + 26^2 ∨
    x = 12^2 + 24^2 + 36^2 ∨ x = 11^2 + 12^2 + 132^2)} = {17689} := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the set
      rintro ⟨n, rfl, h⟩
      rcases h with (h | h | h | h)
      · -- First expression: 11^2 + 13^2 + 17^2
        have h1 : (n ^ 2 : ℕ) = (11^2 + 13^2 + 17^2 : ℕ) := by 
          omega 
        have h1' : (n ^ 2 : ℕ) = 579 := by
          norm_num at h1 ⊢ 
          omega 
        have h4 : n ≤ 32 := by 
          nlinarith 
        interval_cases n <;> omega 
      · -- Second expression: 24^2 + 25^2 + 26^2
        have h1 : (n ^ 2 : ℕ) = (24^2 + 25^2 + 26^2 : ℕ) := by 
          omega 
        have h1' : (n ^ 2 : ℕ) = 1877 := by 
          norm_num at h1 ⊢ 
          omega 
        have h4 : n ≤ 45 := by 
          nlinarith 
        interval_cases n <;> omega 
      · -- Third expression: 12^2 + 24^2 + 36^2
        have h1 : (n ^ 2 : ℕ) = (12^2 + 24^2 + 36^2 : ℕ) := by 
          omega 
        have h1' : (n ^ 2 : ℕ) = 2016 := by 
          norm_num at h1 ⊢ 
          omega 
        have h4 : n ≤ 47 := by 
          nlinarith 
        interval_cases n <;> omega 
      · -- Fourth expression: 11^2 + 12^2 + 132^2
        have h1 : (n ^ 2 : ℕ) = (11^2 + 12^2 + 132^2 : ℕ) := by 
          omega 
        -- This expression is a perfect square: 11² + 12² + 132² = 121 + 144 + 17424 = 17689 = 133²
        have h1' : (n ^ 2 : ℕ) = 17689 := by 
          norm_num at h1 ⊢ 
          omega 
        have h2 : (n : ℕ) = 133 := by
          nlinarith
        omega 
    · -- Show that 17689 is in the set 
      intro hx 
      rw [hx] 
      use 133 
      all_goals norm_num 
  rw [h1] 
  simp [Set.encard_singleton]