import Mathlib

/- Prove that for any integer $n$ the number $n (n^2 + 5)$ is divisible by $6$. -/
theorem number_theory_47061 (n : ℤ) : 6 ∣ n * (n ^ 2 + 5) := by
  apply Int.dvd_of_emod_eq_zero
  have h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h with (h | h | h | h | h | h) <;> simp [h, pow_two, Int.mul_emod, Int.add_emod]