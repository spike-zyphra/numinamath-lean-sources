import Mathlib

theorem number_theory_8027 (n : ℤ) : Int.gcd (12*n + 5) (9*n + 4) = 1 := by
  have h1 : Int.gcd (12 * n + 5) (9 * n + 4) = 1 := by 
    rw [Int.gcd_eq_one_iff_coprime]
    show IsCoprime (12 * n + 5) (9 * n + 4)
    use -3, 4
    all_goals ring
  exact h1