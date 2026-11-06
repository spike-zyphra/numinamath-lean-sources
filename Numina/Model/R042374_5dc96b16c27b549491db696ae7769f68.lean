import Mathlib

theorem algebra_151372 (a b c : ℤ) :
    a > 0 ∧ b > 0 ∧ c > 0 ∧ (8 * a - 5 * b) ^ 2 + (3 * b - 2 * c) ^ 2 + (3 * c - 7 * a) ^ 2 = 2 ↔
    (a, b, c) = (3, 5, 7) ∨ (a, b, c) = (12, 19, 28) := by
  constructor
  · -- Forward direction: if we have positivity and the equation, then it's one of the two triples
    rintro ⟨ha, hb, hc, heq⟩
    have h1 : (8 * a - 5 * b) ≤ 1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]

    have h2 : (8 * a - 5 * b) ≥ -1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]

    have h3 : (3 * b - 2 * c) ≤ 1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]
    have h4 : (3 * b - 2 * c) ≥ -1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]

    have h5 : (3 * c - 7 * a) ≤ 1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]
    have h6 : (3 * c - 7 * a) ≥ -1 := by
      nlinarith [sq_nonneg (8 * a - 5 * b), sq_nonneg (3 * b - 2 * c), sq_nonneg (3 * c - 7 * a), heq]

    have h7 : (8 * a - 5 * b) = -1 ∨ (8 * a - 5 * b) = 0 ∨ (8 * a - 5 * b) = 1 := by omega
    have h8 : (3 * b - 2 * c) = -1 ∨ (3 * b - 2 * c) = 0 ∨ (3 * b - 2 * c) = 1 := by omega
    have h9 : (3 * c - 7 * a) = -1 ∨ (3 * c - 7 * a) = 0 ∨ (3 * c - 7 * a) = 1 := by omega
    rcases h7 with (h7 | h7 | h7) <;> rcases h8 with (h8 | h8 | h8) <;> rcases h9 with (h9 | h9 | h9) <;> 
    simp [h7, h8, h9] at heq ⊢
    <;> norm_num [Prod.ext_iff] at *
    <;> try { 
      omega
    }
  · -- Backward direction
    rintro (h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num -- a > 0
      constructor 
      · norm_num -- b > 0 
      constructor 
      · norm_num -- c > 0 
      all_goals norm_num 
    · -- Second solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num -- a > 0
      constructor 
      · norm_num -- b > 0 
      constructor 
      · norm_num -- c > 0 
      all_goals norm_num