import Mathlib

theorem number_theory_79016 :
    IsLeast {x | ∃ a b p q : ℕ, a > 0 ∧ b > 0 ∧ a ≠ b ∧ 20 * a + 17 * b = p ∧ 17 * a + 20 * b = q ∧ p.Prime ∧ q.Prime ∧ x = p + q} 296 := by
  constructor 
  · -- Show 296 is in the set.
    use 1, 7, 139, 157
    all_goals norm_num 
  · -- Show no smaller element is in the set.
    intro x hx
    rcases hx with ⟨a, b, p, q, ha, hb, hne, hp_eq, hq_eq, hp, hq, hx⟩
    by_contra h
    push_neg at h
    have h1 : p + q < 296 := by linarith
    have h2 : a + b < 8 := by
      omega
    have h3 : a ≤ 7 := by 
      omega
    have h4 : b ≤ 7 := by 
      omega
    interval_cases a <;> interval_cases b
    <;> norm_num [hp_eq, hq_eq] at hp hq hp_eq hq_eq hx 
    <;> try { 
      rw [eq_comm] at hp_eq 
      rw [eq_comm] at hq_eq 
      rw [hp_eq] at hp 
      rw [hq_eq] at hq 
      norm_num at hp hq 
      all_goals try { contradiction } 
    }