import Mathlib

open Real
open scoped BigOperators

theorem algebra_119060 {a : ℕ → ℝ} (ha : ∀ n, a n = 100 ^ n / Nat.factorial n) :
    ∃ N, ∀ n, N ≤ n → a n > a (n + 1) := by
  use 100
  intro n hn
  have h1 : a n = (100 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
    specialize ha n
    simpa using ha
  have h2 : a (n + 1) = (100 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    specialize ha (n + 1)
    simpa using ha
  rw [h1, h2]
  have h4 : (Nat.factorial (n + 1) : ℝ) = (Nat.factorial n * (n + 1) : ℝ) := by
    simp [Nat.factorial]
    <;> ring_nf <;> simp [Nat.factorial]
    <;> ring_nf
    <;> simp [Nat.factorial]
  have h5 : (100 : ℝ) ^ (n + 1) = (100 ^ n * 100 : ℝ) := by
    ring_nf
  rw [h4, h5]
  have h6 : ( (100 : ℝ) ^ n / (Nat.factorial n : ℝ) ) - ( (100 ^ n * (100 : ℝ) ) / ( (Nat.factorial n * (n + 1) : ℝ) ) ) > 0 := by
    have h7 : (n + 1 : ℝ) > (100 : ℝ) := by 
      have h8 : n ≥ 100 := by linarith
      have h10 : (n : ℝ) ≥ (100 : ℝ) := by exact_mod_cast h8
      linarith
    have h8 : ( (n + 1 : ℝ) - (100 : ℝ) ) > 0 := by 
      linarith
    have h10 : (Nat.factorial n : ℝ) > 0 := by
      positivity
    have h9 : ( (100 : ℝ) ^ n / (Nat.factorial n : ℝ) ) - ( (100 ^ n * (100 : ℝ) ) / ( (Nat.factorial n * (n + 1) : ℝ) ) ) = ( (100 : ℝ) ^ n / (Nat.factorial n : ℝ) ) * ( ( (n + 1 : ℝ) - 100 ) / ( (n + 1 ) : ℝ ) ) := by
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring_nf
      all_goals try positivity
      all_goals try linarith
    rw [h9]
    apply mul_pos
    · -- Show that (100^n / n!) > 0
      positivity
    · -- Show that ( (n + 1 ) - 100 ) / (n + 1 ) > 0
      apply div_pos
      linarith
      have h11 : (n + 1 : ℝ) > 0 := by
        have h12 : n ≥ 100 := by linarith
        have h13 : (n : ℝ) ≥ (100 : ℝ) := by exact_mod_cast h12
        linarith
      linarith
  linarith
  all_goals try positivity
  all_goals try positivity