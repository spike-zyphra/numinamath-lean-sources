import Mathlib

theorem number_theory_172824 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a > n ∧ b > n ∧ c > n ∧
      a ∣ (b * c - 1) ∧ b ∣ (a * c + 1) ∧ c ∣ (a * b + 1) := by
  intro n 
  use (n + 1) 
  use (n + 2) 
  use ( (n + 1) ^ 2 + (n + 1) + 1 ) 
  constructor
  · -- Show a > n
    omega
  constructor
  · -- Show b > n
    omega
  constructor
  · -- Show c > n
    nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ))]
  constructor
  · -- Show a divides b*c - 1
    use ( (n + 1) ^ 2 + 2 * (n + 1) + 2 ) 
    ring_nf 
    <;> omega 
  constructor
  · -- Show b divides a*c + 1
    use (n ^ 2 + 2 * n + 2 ) 
    ring_nf 
    <;> omega 
  · -- Show c divides a*b + 1
    use 1 
    all_goals 
      ring_nf 
      <;> omega