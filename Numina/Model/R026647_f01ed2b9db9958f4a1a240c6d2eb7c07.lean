import Mathlib

open Finset Real Nat

theorem algebra_141581 {a : ℕ → ℝ} (ha : ∀ n, a n = 100 ^ n / n !) :
    ∃ N, ∀ n, N ≤ n → a n > a (n + 1) := by
  use 101
  intro n hn
  have h1 : a n = (100 : ℝ) ^ n / n ! := by
    apply ha
  have h2 : a (n + 1) = (100 : ℝ) ^ (n + 1) / (n + 1) ! := by
    apply ha
  rw [h1, h2]
  have h5 : ((100 : ℝ) ^ (n + 1) / ((n + 1) ! : ℝ)) = ((100 : ℝ) ^ n / (n ! : ℝ)) * (100 / ((n + 1 : ℕ) : ℝ)) := by
    field_simp [Nat.factorial]
    <;> ring_nf <;> field_simp <;> ring_nf
  rw [h5]
  have h6 : (100 : ℝ) ^ n / (n ! : ℝ) > 0 := by
    positivity
  have h8 : (100 / ((n + 1 : ℕ) : ℝ)) < 1 := by
    have h61 : (↑(n + 1 : ℕ) : ℝ) ≥ (102 : ℝ) := by 
      have h33 : (↑(n + 1 : ℕ) : ℝ) = (↑n + 1 : ℝ) := by simp
      rw [h33]
      have hn1 : (↑n : ℝ) ≥ (101 : ℝ) := by exact_mod_cast (show n ≥ 101 by linarith)
      nlinarith
    have h62 : (100 / ((n + 1 : ℕ) : ℝ) ) < (1 : ℝ) := by
      have h61' : (↑(n + 1 : ℕ) : ℝ) ≥ (102 : ℝ) := h61
      have h63 : (↑(n + 1 : ℕ) : ℝ) > (0 : ℝ) := by nlinarith
      apply  (div_lt_iff₀ h63).mpr
      nlinarith
    linarith
  have h11 : (100 : ℝ) ^ n / (n ! : ℝ) * (100 / ((n + 1 : ℕ) : ℝ)) < (100 : ℝ) ^ n / (n ! : ℝ) := by
    nlinarith [h6, h8]
  linarith