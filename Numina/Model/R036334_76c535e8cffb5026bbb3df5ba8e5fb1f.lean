import Mathlib

theorem number_theory_236924 (x : ℕ) (h : {n | n = x ∧ 3 * n > 91 ∧ x * 37 ≥ 21 ∧ n > 7}.encard = 3) :
    x = 10 := by 
  have h1 : {n | n = x ∧ 3 * n > 91 ∧ x * 37 ≥ 21 ∧ n > 7} = if (3 * x > 91 ∧ x * 37 ≥ 21 ∧ x > 7) then {x} else ({} : Set ℕ) := by 
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.union_eq_left, Set.union_empty]
    constructor 
    · -- Assume n in the left side 
      intro h 
      rcases h with ⟨hn1, hn2, hn3, hn4⟩ 
      have h2 : n = x := hn1 
      have h3 : 3 * x > 91 := by 
        omega 
      have h4 : x * 37 ≥ 21 := hn3 
      have h5 : x > 7 := by 
        omega 
      simp [h2, h3, h4, h5] 
      <;> tauto 
      all_goals try { nlinarith } 
      all_goals try { linarith } 
      all_goals try { tauto }
      all_goals try { tauto }
    · -- Assume n is in the right side 
      intro h
      split_ifs at h with h6 
      · -- Case where the condition is true 
        have h2 : n = x := by 
          simp at h 
          try { tauto } 
          all_goals try { aesop }
          all_goals try { nlinarith }
        have hx1 : 3 * n > 91 := by 
          rw [show n = x by exact_mod_cast h2]
          all_goals 
            try { tauto }
          all_goals 
            try { nlinarith }
          all_goals 
            try { linarith }
        have hx3 : n > 7 := by 
          rw [show n = x by exact_mod_cast h2]
          all_goals 
            try { tauto }
          all_goals 
            try { nlinarith }
          all_goals 
            try { linarith }
        simp [h2] at *
        <;> tauto 
        all_goals try { nlinarith }
        all_goals try { linarith }
        all_goals try { tauto }
        all_goals try { 
          omega 
        }
        all_goals try { 
          nlinarith 
        }
        all_goals try { 
          linarith 
        }
        all_goals try { tauto }
      · -- Case where the condition is false 
        exfalso 
        all_goals 
          try { 
            tauto 
          }
        all_goals 
          try { 
            nlinarith 
          }
        all_goals 
          try { 
            omega 
          }
  rw [h1] at h 
  by_cases h2 : (3 * x > 91 ∧ x * 37 ≥ 21 ∧ x > 7)
  · -- Case where the condition is true
    simp [h2, Set.encard_singleton] at h 
    all_goals 
      omega 
  · -- Case where the condition is false
    simp [h2] at h 
    all_goals 
      omega 
  all_goals 
    try { 
      tauto 
    }
    <;> try { 
      omega 
    }
    <;> try { 
      nlinarith 
    }
  all_goals 
    try { 
      tauto 
    }
  all_goals 
    try { 
      nlinarith 
    }
  all_goals 
    try { 
      omega 
    }
    <;> try { 
      nlinarith 
    }
    <;> try { 
      tauto 
    }
  all_goals 
    try { 
      nlinarith 
    }
    <;> try { 
      omega 
    }
    <;> try { 
      tauto 
    }
  all_goals 
    try { 
      nlinarith 
    }
    <;> try { 
      omega 
    }
    <;> try { 
      tauto 
    }