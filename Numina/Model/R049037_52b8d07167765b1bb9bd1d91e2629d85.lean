import Mathlib

theorem number_theory_2875
    (a b c : ℤ)
    (h₀ : 0 < c)
    (h₁ : a % c = b % c) :
    (a - b) % c = 0 := by
  have h2 : (a - b) % c = (a % c - b % c) % c := by 
    simp [Int.sub_emod]
    all_goals omega
  rw [h2]
  rw [h₁]
  simp