import Mathlib

theorem number_theory_4143 :
  IsGreatest {x : ℕ | ∃ y z : ℕ, Nat.Prime x ∧ Nat.Prime y ∧ Nat.Prime z ∧ x + y + z = 39} 31 := by
  constructor
  · -- Show 31 is in the set
    use 3, 5
    all_goals norm_num
  · -- Show 31 is greatest
    intro x hx
    rcases hx with ⟨y, z, hx1, hy1, hz1, hsum⟩
    by_contra h
    push_neg at h
    have h1 : x ≥ 32 := by linarith
    have h2 : y + z ≤ 7 := by linarith
    have h3 : y ≤ 7 := by
      by_contra h4
      push_neg at h4
      have h4' : y + z > 7 := by
        linarith
      omega
    have h4 : z ≤ 7 := by
      by_contra h5
      push_neg at h5
      have h5' : y + z > 7 := by
        linarith
      omega
    interval_cases y <;> interval_cases z
    <;> try { 
      have h5 : x ≤ 39 := by omega 
      interval_cases x <;> norm_num at hx1 hy1 hz1 hsum h1 h2 ⊢ <;> all_goals try { contradiction } 
    }
    <;> norm_num at hx1 hy1 hz1 hsum h1 h2 ⊢
    <;> all_goals try { contradiction }
    <;> omega