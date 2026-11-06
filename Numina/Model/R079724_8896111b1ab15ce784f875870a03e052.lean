import Mathlib

theorem number_theory_191883 (n : ℕ) :
    11 ∣ 6^(2*n) + 3^(n + 2) + 3^n := by 
  have h : ∀ n : ℕ, 11 ∣ 6 ^ (2 * n) + 3 ^ (n + 2) + 3 ^ n := by 
    intro n 
    induction n with 
    | zero =>
      norm_num 
    | succ n ih =>
      have h2 : 6 ^ (2 * (n + 1)) = (6 ^ (2 * n)) * 36 := by 
        ring_nf
        <;> simp [pow_mul]
        <;> ring 
      have h3 : 3 ^ ((n + 1) + 2) = (3 ^ (n + 2)) * 3 := by 
        ring_nf 
        <;> simp [pow_succ] 
        <;> ring 
      have h4 : 3 ^ (n + 1) = (3 ^ n) * 3 := by 
        ring_nf 
      rw [h2, h3, h4] 
      omega 
  exact h n