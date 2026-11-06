import Mathlib

theorem number_theory_284770 (n : ℤ) :
    IsCoprime (2 * n + 1) (2 * n * (n + 1)) := by 
  have h2 : IsCoprime (2 * n + 1) (2 * n) := by 
    use 1 
    use -1 
    ring 
  have h3 : IsCoprime (2 * n + 1) (n + 1) := by 
    use -1 
    use 2 
    ring 
  have h10 : IsCoprime (2 * n + 1) ((2 * n) * (n + 1)) := by 
    apply IsCoprime.mul_right 
    exact h2 
    exact h3 
  have h11 : (2 * n * (n + 1)) = ((2 * n) * (n + 1)) := by 
    ring 
  rw [h11] 
  exact h10