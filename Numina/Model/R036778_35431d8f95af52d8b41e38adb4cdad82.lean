import Mathlib

theorem number_theory_258084 (n : ℕ) (hn : n > 0) :
    ∃ k, ∃ m, m > 0 ∧ (k * n + m) % n = 0 ↔ ∃ l, n = 2 ^ l := by
  by_cases h : ∃ l, n = 2 ^ l 
  · -- Assume ∃ l, n = 2 ^ l
    rcases h with ⟨l, rfl⟩
    use 0 
    use 2 ^ l 
    simp
    <;> try { use l <;> try { trivial } <;> try { tauto } }
    <;> try { exfalso <;> try { tauto } }
    <;> try { native_decide }
  · -- Now ¬∃ l, n = 2 ^ l
    push_neg at h 
    -- Set k = 0, m = 0
    use 0 
    use 0 
    simp at *
    <;> try { 
      exfalso 
      have h' := h 0 
      norm_num at h' 
      all_goals tauto 
    }
    <;> try { 
      exfalso 
      have h' := h (0) 
      norm_num at h' 
      all_goals tauto
      <;> norm_num 
      all_goals tauto
    }
    <;> try { 
      exfalso 
      specialize h 0 
      norm_num at h 
      all_goals tauto 
    }
    <;> try { 
      exfalso 
      all_goals try { norm_num } <;> tauto
    }
    <;> try { 
      have h' := h 0 
      norm_num at h' 
    }
    <;> try { 
      exfalso 
      all_goals try { 
        have h' := h 0 
        norm_num at h' 
        contradiction 
      }
    }
    <;> try { 
      have h' := h 0 
      norm_num at h' 
      all_goals tauto 
    }
    <;> try { 
      exfalso 
      all_goals try { 
        have h' := h 0 
        norm_num at h' 
        contradiction 
      }
    }
    <;> try { 
      exfalso 
      all_goals try { 
        contradiction 
      }
    }