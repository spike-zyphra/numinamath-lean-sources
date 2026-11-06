import Mathlib

  theorem number_theory_186816 : ¬ Prime (4^9 + 6^10 + 3^20) := by
    have h1 : (4^9 + 6^10 + 3^20 : ℕ) = (59561 : ℕ) ^ 2 := by
      norm_num

    rw [h1]

    have h3 : (59561 : ℕ) > 1 := by
      norm_num
    apply not_prime_pow 
    all_goals 
      norm_num at h3 ⊢ 
      <;> try { nlinarith }