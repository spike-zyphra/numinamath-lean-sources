import Mathlib

theorem number_theory_255857 (n : ℤ) :
    ¬(15 ∣ (n - 6) ∧ 24 ∣ (n - 5)) := by 
  intro h
  rcases h with ⟨h1, h2⟩
  have h3 : n % 3 = 0 := by
    omega
  have h4 : n % 3 = 2 := by
    omega
  omega