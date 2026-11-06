import Mathlib

theorem number_theory_284972 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (h : ∑ i ∈ Finset.range (800 - m - n), (Nat.digits 10 (2345 * 10 ^ i)).headI = 2345) :
    m + n = 130 := by 
  have h₁ : 800 - m - n > 0 := by 
    by_cases h₂ : m + n < 800 
    · 
      omega 
    · 
      -- Case m + n >= 800
      have h₂₂ : m + n >= 800 := by 
        omega 
      have h₂₃ : 800 - m - n = 0 := by 
        omega 
      rw [show Finset.range (800 - m - n) = Finset.range 0 by rw [h₂₃]] at h 
      simp at h 
      all_goals linarith 
  have h₂ : ∀ (k : ℕ), k > 0 → (∑ i ∈ Finset.range k, (Nat.digits 10 (2345 * 10 ^ i)).headI = 5) := by 
    intro k hk
    have : ∀ (k : ℕ), k > 0 → (∑ i ∈ Finset.range k, (Nat.digits 10 (2345 * 10 ^ i)).headI = 5) := by 
      intro k hk
      induction k with 
      | zero => 
        linarith 
      | succ k ih => 
        cases k with 
        | zero => 
          simp 
        | succ k => 
          norm_num [Finset.sum_range_succ] at ih ⊢
          <;> try { 
            have h_a : (Nat.digits 10 (2345 * 10 ^ (k + 1))).headI = 0 := by 
              simp [Nat.digits, Nat.digitsAux] 
              <;> try { norm_num } 
              <;> try { linarith } 
            simp [h_a] 
          }
          <;> try { linarith [ih] }
          <;> try { 
            have h_0 : (Nat.digits 10 (2345 * 10 ^ (k + 1))).headI = 0 := by 
              simp [Nat.digits, Nat.digitsAux] 
              <;> try { norm_num } 
            simp [h_0] at * 
            <;> try { linarith } 
          }
          <;> try { omega } 
          <;> try { tauto } 
          <;> try { 
            have : (Nat.digits 10 (2345 * 10 ^ (k + 1))).headI = 0 := by 
              simp [Nat.digits, Nat.digitsAux] 
              <;> try { norm_num } 
            simp [this] at * 
            <;> try { linarith } 
          }
          <;> try { linarith } 
          all_goals try { 
            have : (Nat.digits 10 (2345 * 10 ^ (k + 1))).headI = 0 := by 
              simp [Nat.digits, Nat.digitsAux] 
              <;> try { norm_num } 
            simp [this] at * 
          }
          <;> try { linarith } 
    apply this k hk 
  have h₂₂ : ∑ i ∈ Finset.range (800 - m - n), (Nat.digits 10 (2345 * 10 ^ i)).headI = 5 := h₂ (800 - m - n) h₁ 
  linarith [h, h₂₂] 
  all_goals try { try { try { try { contradiction } } } }