import Mathlib

theorem number_theory_262811 (m n : ℕ) :
    (Nat.digits 10 m).sum + n = 70 ∧ (Nat.digits 10 n).sum + m = 70 ↔
    (m = 56 ∧ n = 59) ∨ (m = 57 ∧ n = 58) ∨ (m = 58 ∧ n = 57) ∨
    (m = 59 ∧ n = 56) ∨ (m = 60 ∧ n = 64) ∨ (m = 61 ∧ n = 63) ∨
    (m = 62 ∧ n = 62) ∨ (m = 63 ∧ n = 61) ∨ (m = 64 ∧ n = 60) := by
  constructor
  · -- Forward implication: if the equations hold, then (m, n) is one of the listed pairs.
    rintro ⟨h1, h2⟩
    have h3 : m ≤ 70 := by 
      omega
    have h4 : n ≤ 70 := by 
      omega
    interval_cases m <;> try { 
      omega 
      <;> try { 
        interval_cases n <;> norm_num at h1 h2 ⊢ <;> tauto 
      }
    }
    <;> norm_num at h1 h2 ⊢ 
    <;> try { 
      interval_cases n <;> norm_num at h1 h2 ⊢ <;> tauto 
    }
  · -- Backward implication: if (m, n) is one of the listed pairs, then the equations hold.
    rintro (h | h | h | h | h | h | h | h | h)
    · -- Check the first pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the second pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the third pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the fourth pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the fifth pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the sixth pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the seventh pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the eighth pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- Check the ninth pair
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num