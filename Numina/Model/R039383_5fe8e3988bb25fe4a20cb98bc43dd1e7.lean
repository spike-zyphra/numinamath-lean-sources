import Mathlib

open Polynomial
theorem algebra_266099 (n : ℕ) (hn : n > 0) :
    (X ^ 2 - X + 1 : Polynomial ℤ) ∣ X ^ (2 * n + 1) + (X - 1) ^ (n + 2) := by
  induction n with
  | zero => 
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero => 
      use (2 * X - 1)
      ring_nf
      <;> norm_num
    | succ n => 
      have eq1 : (X : Polynomial ℤ) ^ (2 * (n + 1 + 1) + 1) + (X - 1) ^ ((n + 1 + 1) + 2) = (X - 1) * ((X : Polynomial ℤ) ^ (2 * (n + 1) + 1) + (X - 1) ^ ((n + 1) + 2)) + (X) ^ (2 * (n + 1) + 1) * (X ^ 2 - X + 1) := by
        ring_nf
        <;> zify
        <;> ring_nf
        <;> omega
      rw [eq1]
      apply dvd_add
      · 
        apply dvd_mul_of_dvd_right
        apply ih <;> omega
      · 
        apply dvd_mul_left
        all_goals norm_num
        all_goals ring_nf <;> norm_num
        all_goals omega