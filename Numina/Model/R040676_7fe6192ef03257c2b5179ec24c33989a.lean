import Mathlib

theorem number_theory_37517 :
    ∃ s : Finset ℕ, s.card = 1 ∧ ∃ x ∈ s, x = 2 ∧
    ∃ t : Finset ℕ, t.card = 1 ∧ ∃ x ∈ t, x = 1000 := by 
  use {2}
  constructor 
  · -- Show that s has cardinality 1
    simp
  · -- Show that 2 belongs to s 
    use 2 
    constructor 
    · -- Show that 2 ∈ {2}
      simp 
    · -- Show that 2 = 2 
      constructor 
      · rfl 
      · -- Show that t has cardinality 1 
        use {1000} 
        constructor 
        · -- Show that t has cardinality 1 
          simp 
        · -- Show that 1000 ∈ t 
          use 1000 
          constructor 
          · -- Show that 1000 ∈ {1000} 
            simp 
          · -- Show that 1000 = 1000 
            all_goals rfl