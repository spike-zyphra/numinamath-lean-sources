import Mathlib

theorem number_theory_101842 (n : ℕ) : (n - 1) ∣ (n^2 + n - 2) := by 
  have h1 : n ^ 2 + n - 2 = (n - 1) * (n + 2) := by
    cases n with
    | zero =>
      all_goals 
        omega
    | succ n =>
      cases n with
      | zero =>
        all_goals 
          omega
      | succ n =>
        simp [Nat.mul_add, Nat.mul_sub, Nat.add_mul, Nat.mul_assoc]
        <;> ring_nf
        <;> omega
  rw [h1]
  all_goals 
    use n + 2
    all_goals 
      ring