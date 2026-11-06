import Mathlib

theorem number_theory_115341 (x y : ℕ) :
    Nat.factorial x + 12 = y^2 ↔ (x = 4 ∧ y = 6) := by
  constructor
  · -- Assume Nat.factorial x + 12 = y^2, prove (x = 4 ∧ y = 6)
    intro h
    by_cases h1 : x ≤ 6
    · -- x ≤ 6
      interval_cases x <;> try { 
        simp [Nat.factorial] at h 
        all_goals 
          have : y ≤ 32 := by nlinarith 
          interval_cases y <;> omega 
      }
    · -- x > 6 
      have h2 : x ≥ 7 := by omega 
      have h3 : 5 ∣ Nat.factorial x := by 
        apply Nat.dvd_factorial 
        all_goals omega 
      have h4 : y^2 % 5 = 0 ∨ y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
        have h1 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
          omega 
        rcases h1 with (h1 | h1 | h1 | h1 | h1) 
        · -- y % 5 = 0 
          simp [Nat.pow_mod, h1] 
        · -- y % 5 = 1 
          simp [Nat.pow_mod, h1] 
        · -- y % 5 = 2 
          simp [Nat.pow_mod, h1] 
        · -- y % 5 = 3 
          simp [Nat.pow_mod, h1] 
        · -- y % 5 = 4 
          simp [Nat.pow_mod, h1] 
      have h5 : (Nat.factorial x + 12) % 5 = 2 := by 
        have h5 : Nat.factorial x % 5 = 0 := by 
          have h5 : x ≥ 5 := by omega 
          have h6 : 5 ∣ Nat.factorial x := by 
            apply Nat.dvd_factorial 
            all_goals omega 
          omega 
        omega 
      have h6 : y^2 % 5 = 2 := by 
        omega 
      omega 
  · -- Assume (x = 4 ∧ y = 6), prove Nat.factorial x + 12 = y^2 
    rintro ⟨hx, hy⟩ 
    rw [hx, hy] 
    norm_num [Nat.factorial]