import Mathlib

theorem number_theory_255863 (n : ℕ) :
    19 ∣ 5^(2*n + 1) * 2^(n + 2) + 3^(n + 2) * 2^(2*n + 1) := by 
  have h1 : ∀ (n : ℕ), 19 ∣ 5^(2*n + 1) * 2^(n + 2) + 3^(n + 2) * 2^(2*n + 1) := by 
    intro n 
    induction n with 
    | zero => 
      norm_num 
    | succ k ih => 
      have eq1 : 5^(2 * (k + 1) + 1) * 2^((k + 1) + 2) + 3^((k + 1) + 2) * 2^(2 * (k + 1) + 1) = 50 * (5^(2 * k + 1) * 2^(k + 2)) + 12 * (3^(k + 2) * 2^(2 * k + 1)) := by 
        ring_nf 
      rw [eq1] at *
      omega 
  specialize h1 n 
  simpa using h1