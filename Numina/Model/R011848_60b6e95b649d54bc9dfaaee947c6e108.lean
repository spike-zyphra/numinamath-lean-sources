import Mathlib

theorem algebra_64758 {A B : ℕ} (hA : A ∈ Finset.Icc 10 99) (hB : B ∈ Finset.Icc 100 999) :
    A * (1 + B / 100 : ℚ) = B * (1 - A / 100 : ℚ) ↔
    (A, B) ∈ ({(40, 200), (45, 450), (46, 575)} : Finset (ℕ × ℕ)) := by 
  rw [Finset.mem_Icc] at hA hB
  constructor
  · -- Forward implication: equation implies the three pairs 
    intro h
    rcases hA with ⟨ha1, ha2⟩
    rcases hB with ⟨hb1, hb2⟩
    have eq1 : (A : ℚ) * (1 + (B : ℚ) / 100) = (B : ℚ) * (1 - (A : ℚ) / 100) := by 
      simpa using h
    have eq2 : (A : ℚ) * (100 + (B : ℚ)) = (B : ℚ) * (100 - (A : ℚ)) := by
      field_simp at eq1 ⊢ 
      linarith 
    have eq3 : (A : ℤ) * (100 + (B : ℤ)) = (B : ℤ) * (100 - (A : ℤ)) := by
      exact_mod_cast eq2 
    have eq4 : (A : ℤ) * (100 + (B : ℤ)) = (B : ℤ) * (100 - (A : ℤ)) := eq3 
    have eq6 : A ≤ 99 := by linarith 
    have eq7 : B ≤ 999 := by linarith 
    have eq8 : A ≥ 10 := by linarith 
    have eq9 : B ≥ 100 := by linarith 
    simp [Finset.mem_insert, Finset.mem_singleton]
    interval_cases A <;> omega 
  · -- Backward implication: each pair satisfies the equation 
    intro h 
    have h2 : A = 40 ∧ B = 200 ∨ A = 45 ∧ B = 450 ∨ A = 46 ∧ B = 575 := by 
      simpa using h 
    rcases h2 with (h | h | h) 
    · -- Check (40, 200) 
      have eq1 : (A : ℚ) = 40 := by 
        have h1 : A = 40 := by 
          omega 
        exact_mod_cast h1 
      have eq2 : (B : ℚ) = 200 := by 
        have h1 : B = 200 := by 
          omega 
        exact_mod_cast h1 
      rw [eq1, eq2]
      norm_num 
    · -- Check (45, 450) 
      have eq1 : (A : ℚ) = 45 := by 
        have h1 : A = 45 := by 
          omega 
        exact_mod_cast h1 
      have eq2 : (B : ℚ) = 450 := by 
        have h1 : B = 450 := by 
          omega 
        exact_mod_cast h1 
      rw [eq1, eq2]
      norm_num 
    · -- Check (46, 575) 
      -- Now we need to prove (46 : Q) ... 
      -- Let's adjust our approach here. 
      have eq1 : (A : ℚ) = 46 := by 
        have h1 : A = 46 := by 
          omega 
        exact_mod_cast h1 
      have eq2 : (B : ℚ) = 575 := by 
        have h1 : B = 575 := by 
          omega 
        exact_mod_cast h1 
      rw [eq1, eq2]
      norm_num