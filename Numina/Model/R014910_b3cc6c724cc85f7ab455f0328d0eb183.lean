import Mathlib

theorem number_theory_211534 : Prime (4^9 + 6^10 + 3^20) ↔ False := by
  have h1 : ¬ Prime (4^9 + 6^10 + 3^20) := by 
    rw [show 4^9 + 6^10 + 3^20 = (2^9 + 3^10) ^ 2 by norm_num]
    apply not_prime_pow
    all_goals
      native_decide
  simp [h1]
  all_goals
    try tauto