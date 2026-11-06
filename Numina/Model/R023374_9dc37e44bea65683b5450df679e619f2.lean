import Mathlib

theorem number_theory_261501 (n : ℕ) :
    ∃ m, m^2 = 2^10 + 2^13 + 2^14 + 3 * 2^n ↔ n = 13 ∨ n = 15 := by
  by_cases h13 : n = 13
  · -- Assume n = 13, let m = 224
    use 224
    simp [h13]
    <;> norm_num
  · -- Assume n = 15
    by_cases h2 : n = 15
    · -- Assume n = 15, let m = 352
      use 352
      simp [h2]
      <;> norm_num
    · -- Assume n ≠ 13 and n ≠ 15
      use 0
      have h14 : ¬ n = 13 := by 
        omega 
      have h15 : ¬ n = 15 := by 
        omega
      have h4 : ¬(n = 13 ∨ n = 15) := by 
        omega 
      constructor 
      · -- Assume 0 = 2^10 + 2^13 + 2^14 + 3 * 2^n (LHS), prove RHS (n = 13 ∨ n = 15)
        intro h0 
        have eq1 : 2^10 + 2^13 + 2^14 + 3 * 2^n = (25600 + 3 * 2^n : ℕ) := by 
          ring_nf 
        have h5 : 0 = 25600 + 3 * 2^n := by 
          linarith [h0, eq1] 
        have h5' : 25600 + 3 * 2^n > 0 := by 
            omega 
        omega 
      · -- Assume RHS, prove LHS
        intro h0 
        rcases h0 with (h13 | h15) 
        · -- Assume n = 13 
          omega 
        · -- Assume n = 15 
          omega