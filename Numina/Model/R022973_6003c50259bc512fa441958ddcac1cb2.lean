import Mathlib

theorem number_theory_294390 {n : ℕ} (hn : n ≥ 2) :
    ∃ a d, a = n.minFac ∧ d > 0 ∧ d ∣ n ∧ n = a^3 + d^3 ↔ n = 16 ∨ n = 72 ∨ n = 520 := by
  by_cases h16 : n = 16
  · -- Case where n = 16
    use 2, 2
    simp [h16]
    <;> norm_num [Nat.minFac]
  by_cases h72 : n = 72
  · -- Case where n = 72
    use 2, 4
    simp [h72]
    <;> norm_num [Nat.minFac]
  by_cases h520 : n = 520
  · -- Case where n = 520
    use 2, 8
    simp [h520]
    <;> norm_num [Nat.minFac]
  push_neg at h16 h72 h520
  use 0, 0
  simp [h16, h72, h520] 
  <;> try { 
    have h2 : n ≥ 2 := by linarith
    all_goals try { 
      omega 
    }
  }