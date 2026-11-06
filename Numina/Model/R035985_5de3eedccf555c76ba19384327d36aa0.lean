import Mathlib

open Real
open scoped BigOperators

theorem algebra_245005 {f : ℕ → ℝ} (hf : ∀ n, f n = 100 ^ n / Nat.factorial n) :
    ∃ N, ∀ n, N ≤ n → f n > f (n + 1) := by
  use 100
  intro n hn
  have h1 : f n = (100 : ℝ) ^ n / Nat.factorial n := hf n
  have h2 : f (n + 1) = (100 : ℝ) ^ (n + 1) / Nat.factorial (n + 1) := hf (n + 1)
  rw [h1, h2]
  have h3 : (100 : ℝ) ^ (n + 1) / Nat.factorial (n + 1) = ((100 : ℝ) ^ n / Nat.factorial n : ℝ) * (100 / (n + 1 : ℝ)) := by
    field_simp [Nat.factorial]
    <;> ring
  rw [h3]
  have h4 : (100 : ℝ) ^ n / Nat.factorial n > 0 := by
    positivity
  have h8 : (100 / (n + 1 : ℝ)) < 1 := by
    have hn1 : n + 1 ≥ 101 := by 
      omega
    have : (n + 1 : ℝ) ≥ (101 : ℝ) := by exact_mod_cast hn1
    apply (div_lt_one (by
      have hn1 : n + 1 ≥ 101 := by 
        omega 
      have : (n + 1 : ℝ) ≥ (101 : ℝ) := by exact_mod_cast hn1
      linarith
    )).mpr
    linarith
  nlinarith [h4, h8]