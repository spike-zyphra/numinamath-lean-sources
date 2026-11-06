import Mathlib

theorem number_theory_165209 : ¬∃ q : ℚ, Real.sqrt 2 = q := by 
  rintro ⟨q, hq⟩
  have h1 : Irrational (Real.sqrt 2) := by 
    apply irrational_sqrt_two
  have h4 : ¬ Irrational (Real.sqrt 2) := by 
    rw [hq]
    simp 
  contradiction