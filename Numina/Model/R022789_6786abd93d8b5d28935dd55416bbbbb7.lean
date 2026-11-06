import Mathlib

theorem number_theory_92686 {n : ℕ} (hn : n ≠ 0) :
    ∃ d : Fin 7 → ℕ,
      (∀ i j, i < j → d i < d j) ∧
      (∀ i, d i ∣ n) ∧
      d 5 ^ 2 + d 6 ^ 2 - 1 = n ↔ n = 144 ∨ n = 1984 := by 
  by_cases h : n = 144 ∨ n = 1984 
  · -- if n = 144 or 1984, then exist such function
    rcases h with (r | r)
    · -- n = 144
      rw [r]
      use λ i => match i with
        | 0 => 1
        | 1 => 2
        | 2 => 3
        | 3 => 4
        | 4 => 6
        | 5 => 8
        | 6 => 9
        | _ => 0
      native_decide
    · -- n = 1984
      rw [r]
      use λ i => match i with
        | 0 => 1
        | 1 => 2
        | 2 => 4
        | 3 => 8
        | 4 => 16
        | 5 => 31
        | 6 => 32
        | _ => 0
      native_decide 
  · -- n ≠ 144 and n ≠ 1984 
    push_neg at h 
    use λ i => 0 
    simp at h ⊢ 
    <;> try { 
      all_goals 
        omega 
    }