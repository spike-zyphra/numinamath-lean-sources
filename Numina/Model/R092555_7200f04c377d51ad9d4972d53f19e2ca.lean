import Mathlib

theorem number_theory_4009 : IsGreatest {x | ∃ a b : ℕ, x = a + b ∧ 11 * a + 41 * b = 2020} 170 := by 
  constructor
  · -- Show 170 in the set
    use 165, 5
    all_goals 
      omega
    <;> try { linarith }
    <;> try { linarith }
  · -- Show greatest
    intro x h
    rcases h with ⟨a, b, h_eq, heq⟩
    by_contra h'
    push_neg at h'
    have h1 : x > 170 := by linarith [h']
    -- we have x = a + b > 170
    rw [show x = a + b by exact h_eq] at h1
    -- or a + b > 170
    have heq' : 11 * a + 41 * b = 2020 := heq
    omega