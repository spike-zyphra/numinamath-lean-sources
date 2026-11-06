import Mathlib

theorem algebra_12115 :
    IsGreatest {x : ℤ | Prime (|6 * x ^ 2 - 47 * x + 15|)} 8 := by 
  constructor
  · -- Show that 8 is in the set
    show Prime (|6 * (8 : ℤ) ^ 2 - 47 * (8 : ℤ) + 15|)
    norm_num
  · -- Show that no integer greater than 8 is in the set
    intro x hx
    have h1 : Prime (|6 * x ^ 2 - 47 * x + 15|) := hx
    by_contra h
    push_neg at h
    have h2 : x ≥ 9 := by omega
    -- Let's factor the polynomial
    have h3 : (6 * x ^ 2 - 47 * x + 15 : ℤ) = (3 * x - 1) * (2 * x - 15) := by
      ring
    have h4 : |6 * x ^ 2 - 47 * x + 15| = |(3 * x - 1) * (2 * x - 15)| := by 
      rw [h3]
    have h5 : |6 * x ^ 2 - 47 * x + 15| = |3 * x - 1| * |2 * x - 15| := by
      rw [h4]
      rw [abs_mul]
    have h6 : |3 * x - 1| > 1 := by
      have h7 : x ≥ 9 := h2
      have h8 : 3 * x - 1 ≥ 26 := by omega
      have h9 : |3 * x - 1| = 3 * x - 1 := by
        rw [abs_of_nonneg]
        omega
      have h10 : |3 * x - 1| ≥ 26 := by linarith [h9, h8]
      linarith
    have h7 : |2 * x - 15| > 1 := by
      have h8 : x ≥ 9 := h2
      have h9 : 2 * x - 15 ≥ 3 := by omega
      have h10 : |2 * x - 15| = 2 * x - 15 := by 
        rw [abs_of_nonneg]
        omega
      have h11 : |2 * x - 15| ≥ 3 := by linarith [h10, h9]
      linarith
    have h8 : Prime (|6 * x ^ 2 - 47 * x + 15|) := h1
    have h9 : |6 * x ^ 2 - 47 * x + 15| = |3 * x - 1| * |2 * x - 15| := h5
    rw [h9] at h8
    have h10 : ¬ Prime (|3 * x - 1| * |2 * x - 15|) := by 
      rw [Int.prime_iff_natAbs_prime]
      have h11 : (|3 * x - 1| * |2 * x - 15| : ℤ) = (|3 * x - 1| : ℤ) * (|2 * x - 15| : ℤ) := by ring
      have h14 : (|3 * x - 1| * |2 * x - 15| : ℤ).natAbs = (|3 * x - 1|).natAbs * (|2 * x - 15|).natAbs := by
        simp [Int.natAbs_mul]
      rw [h14]
      have h14' : (|3 * x - 1|).natAbs > 1 := by 
        omega 
      have h15' : (|2 * x - 15|).natAbs > 1 := by 
        omega
      have h17 : ¬ (Nat.Prime ((|3 * x - 1|).natAbs * (|2 * x - 15|).natAbs : ℕ)) := by 
        apply Nat.not_prime_mul 
        all_goals 
          omega 
      simpa using h17
    contradiction