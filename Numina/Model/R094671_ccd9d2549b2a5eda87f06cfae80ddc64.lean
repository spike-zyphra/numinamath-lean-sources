import Mathlib

theorem number_theory_597700 (b : ℕ) (hb : b > 2) :
    ¬Prime (Nat.ofDigits b [1, 0, 2, 0, 1]) := by
  have h1 : Nat.ofDigits b [1, 0, 2, 0, 1] = (b ^ 2 + 1) ^ 2 := by 
    simp [Nat.ofDigits, add_assoc, mul_add, pow_two, pow_succ]
    <;> ring 
    <;> tauto 
  rw [h1]

  have h2 : b ^ 2 + 1 > 1 := by 
    nlinarith [hb, sq_pos_of_pos (show (0 : ℕ) < b from by linarith)]

  have h3 : ¬ Prime ((b ^ 2 + 1) ^ 2) := by 
    apply not_prime_pow 
    · linarith 
    all_goals linarith 
  exact h3