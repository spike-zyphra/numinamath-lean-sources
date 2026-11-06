import Mathlib

theorem algebra_278670 {n : ℕ} (hn : n^3 - n = 388944 ∨ n^3 - n = 388945 ∨ n^3 - n = 388954 ∨ n^3 - n = 388948) :
    n^3 - n = 388944 := by
  have h1 : n^3 % 6 = n % 6 := by
    have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
      omega
    rcases h1 with (h | h | h | h | h | h) <;> 
    simp [h, pow_succ, Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq]
  have h2 : (n ^ 3 - n) % 6 = 0 := by
    have h1' : n ^ 3 % 6 = n % 6 := h1
    omega
  have h3 : n ^ 3 - n = 388944 ∨ n ^ 3 - n = 388945 ∨ n ^ 3 - n = 388954 ∨ n ^ 3 - n = 388948 := by
    simpa using hn
  omega