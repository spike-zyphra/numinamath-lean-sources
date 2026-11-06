import Mathlib

theorem algebra_13294 (b : ℝ) (hb : b ∈ Set.Icc (-17) 17) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧
      (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^4 + 25 * b^2 = (4 * b^2 - 10 * b) * x1^2 ∧
        x2^4 + 25 * b^2 = (4 * b^2 - 10 * b) * x2^2) ↔ m + n = 63 := by 
  use 0, 0 
  simp 
  all_goals 
    try { 
      norm_num 
      <;> try { 
        nlinarith 
      } 
    } 
    <;> try { 
      tauto 
      <;> try { 
        nlinarith 
      } 
    }
    <;> try { 
      tauto 
    }