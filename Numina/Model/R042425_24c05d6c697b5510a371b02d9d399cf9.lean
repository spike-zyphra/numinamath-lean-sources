import Mathlib

theorem number_theory_218961 : ¬ ∃ n, n^2 = Nat.factorial 100 := by 
  rintro ⟨n, hn⟩ 
  have h1 : ¬ IsSquare (Nat.factorial 100) := by 
    native_decide 
  have h2 : IsSquare (Nat.factorial 100) := by 
    refine ⟨n, by nlinarith⟩ 
  contradiction