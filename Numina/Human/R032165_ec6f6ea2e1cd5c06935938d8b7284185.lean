import Mathlib

theorem number_theory_276074 (n : ℕ) : 23 ∣ 5^(2*n+1) + 2^(n+4) + 2^(n+1) := by 
  induction n with
  | zero =>
    use 1
    <;> norm_num
  | succ k ih =>
    have h : 5 ^ (2 * (k + 1) + 1) + 2 ^ ((k + 1) + 4) + 2 ^ ((k + 1) + 1) = 25 * (5 ^ (2 * k + 1)) + 2 * (2 ^ (k + 4)) + 2 * (2 ^ (k + 1)) := by ring
    rw [h]
    omega