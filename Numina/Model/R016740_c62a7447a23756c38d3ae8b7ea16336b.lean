import Mathlib

theorem number_theory_22758 (x : ℕ) (hx : x = 720) :
    IsLeast {y | ∃ a : ℕ, a > 0 ∧ y^3 = a * x} 60 := by
  rw [hx]
  constructor
  · -- Show that 60 is in the set
    use 300
    all_goals 
      norm_num 
  · -- Show that 60 is the smallest
    intro y hy
    rcases hy with ⟨a, ha, heq⟩
    by_contra h
    push_neg at h
    have h_eq : a * 720 = y ^ 3 := by 
      omega
    have h1 : y ≤ 59 := by 
      omega
    by_cases h4 : y < 10
    · -- y < 10
      interval_cases y <;> try { 
        omega 
      }
    · -- y ≥ 10
      have h4 : y ≥ 10 := by omega
      have h5 : a ≥ 1 := by omega
      interval_cases y <;> try { 
        omega 
      }