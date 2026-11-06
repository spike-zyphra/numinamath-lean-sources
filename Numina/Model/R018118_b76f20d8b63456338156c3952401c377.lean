import Mathlib

theorem number_theory_302695 (n : ℕ) : 1989 ∣ 13 * (-50 : ℤ) ^ n + 17 * (40 : ℤ) ^ n - 30 := by 
  have h1 : ∀ n : ℕ, 1989 ∣ 13 * (-50 : ℤ) ^ n + 17 * (40 : ℤ) ^ n - 30 := by 
    intro n 
    induction n with
    | zero => 
      norm_num 
    | succ n ih => 
      have h2 : (13 * (-50 : ℤ) ^ (n + 1) + 17 * (40 : ℤ) ^ (n + 1) - 30) = 
        (-50 : ℤ) * (13 * (-50 : ℤ) ^ n) + (40 : ℤ) * (17 * (40 : ℤ) ^ n) - 30 := by 
        ring 
      rw [h2] 
      omega 
  specialize h1 n 
  simpa using h1