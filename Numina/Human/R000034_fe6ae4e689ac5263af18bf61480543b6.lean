import Mathlib

/-- 2 divides the product of two  consecutive natural numbers. -/
lemma prod_cons2_dvd2 (n : ℕ) : 2 ∣ n * (n + 1) := by
  by_cases h : n % 2 = 0
  · replace h :=  Nat.dvd_of_mod_eq_zero h
    exact Dvd.dvd.mul_right h (n + 1)
  · have : n % 2 < 2 := Nat.mod_lt n (by linarith)
    have h : n % 2 = 1 := by simp at *; linarith
    have : (n + 1) % 2 = 0 := by rw [Nat.add_mod]; simp [h]
    have := Nat.dvd_of_mod_eq_zero this
    exact Dvd.dvd.mul_left this n

/-- Prove that the difference between the square of a natural number and the number itself is divisible by 2. -/
theorem number_theory_4063 (n : ℕ) : 2 ∣ n ^ 2 - n := by
  by_cases h : n = 0
  · rw [h]; simp
  · -- According to above lemma, $2 \mid (n-1)*n. $
    have := prod_cons2_dvd2 (n - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)] at this
    rw [Nat.sub_one_mul, ←pow_two] at this
    assumption
