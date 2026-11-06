import Mathlib

theorem number_theory_271641 : ¬ ∃ x y, 5^x + 2 = 17^y := by 
  rintro ⟨x, y, h⟩

  have h1 : (5 : ℕ) ^ x % 4 = 1 := by 
    have h1 : ∀ x : ℕ, (5 : ℕ) ^ x % 4 = 1 := by 
      intro x
      induction x with 
      | zero => 
        simp 
      | succ x ih => 
        simp [Nat.pow_succ, Nat.mul_mod, ih] 
    exact h1 x
  
  have h2 : (17 : ℕ) ^ y % 4 = 1 := by 
    have h1 : ∀ y : ℕ, (17 : ℕ) ^ y % 4 = 1 := by 
      intro y 
      induction y with 
      | zero => 
        simp 
      | succ y ih => 
        simp [Nat.pow_succ, Nat.mul_mod, ih] 
    exact h1 y
  
  have h3 : (5 ^ x + 2) % 4 = 3 := by 
    omega 

  have h4 : (5 ^ x + 2) % 4 = (17 ^ y) % 4 := by 
    omega 

  omega