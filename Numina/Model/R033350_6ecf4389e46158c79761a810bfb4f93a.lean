import Mathlib

theorem algebra_260107 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, (i * (i + 1) + (-1 : ℤ)^i) = n * (n + 1) * (n + 2) / 3 + ((-1 : ℤ)^n - 1) / 2 := by 
  have h1 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (i * (i + 1) + (-1 : ℤ)^i) = n * (n + 1) * (n + 2) / 3 + ((-1 : ℤ)^n - 1) / 2 := by
    intro n 
    induction n with 
    | zero =>
      norm_num 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      simp [add_mul, mul_add, pow_two, pow_succ] at *
      all_goals 
        ring_nf at *
        <;> 
        omega
  specialize h1 n 
  simpa using h1