import Mathlib

theorem number_theory_2471
    (n : ℤ) :
    (3 * n) / 3 = n ∧ 3 ∣ (3 * n) := by 
  constructor 
  · -- Prove that (3 * n) / 3 = n 
    have h1 : (3 * n) / 3 = n := by
      have h3 : (3 * n) / 3 = n := by
        rw [Int.ediv_eq_of_eq_mul_left]
        all_goals 
          omega 
      exact h3 
    exact h1
  · -- Prove that 3 divides (3 * n)
    use n
    <;> ring