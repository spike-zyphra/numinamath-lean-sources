import Mathlib

/- Prove that $n^2 + 3n + 5$ is not divisible by $121$ for any positive integer $n$. -/
theorem number_theory_49177 (n : ℕ) (hn : n > 0) :
    ¬ 121 ∣ n^2 + 3 * n + 5 := by 
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have : n % 121 < 121 := Nat.mod_lt n (by linarith)
  interval_cases n % 121 <;> simp_all
  <;> omega