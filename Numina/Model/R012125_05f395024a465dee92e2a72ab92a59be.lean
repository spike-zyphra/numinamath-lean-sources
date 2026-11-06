import Mathlib

theorem number_theory_186204 :
IsGreatest {x:ℕ | ∃a:ℕ, ∃b:ℕ, ∃c:ℕ, a≠b ∧ a≠c ∧ b≠c ∧ a+b+c = 48 ∧ a*b*c = x} 4080 := by 
  constructor 
  · -- Show 4080 is in the set 
    use 15, 16, 17 
    all_goals norm_num 
  · -- Show that 4080 is greatest 
    intro x hx 
    rcases hx with ⟨a, b, c, hab, hac, hbc, hsum, hm⟩ 
    by_contra h 
    push_neg at h 
    have h1 : a ≤ 47 := by omega 
    have h2 : b ≤ 47 := by omega 
    have h3 : c ≤ 47 := by omega 
    interval_cases a <;> interval_cases b <;> omega