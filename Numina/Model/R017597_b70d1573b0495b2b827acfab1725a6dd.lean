import Mathlib

open Real Filter Function
open scoped Topology

theorem calculus_122035 :
  Tendsto (λ n => (Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2)) / Nat.factorial (2 * n + 3)) atTop (𝓝 0) := by
  have h1 : ∀ n : ℕ, (Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2)) / Nat.factorial (2 * n + 3) = 0 := by
    intro n
    have h11 : Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2) < Nat.factorial (2 * n + 3) := by
      have h12 : Nat.factorial (2 * n + 2) = (2 * n + 2) * Nat.factorial (2 * n + 1) := by
        simp [Nat.factorial]
        <;> ring_nf <;> omega
      have h13 : Nat.factorial (2 * n + 3) = (2 * n + 3) * (2 * n + 2) * Nat.factorial (2 * n + 1) := by
        simp [Nat.factorial]
        <;> ring_nf <;> omega
      have h14 : Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2) = (2 * n + 3) * Nat.factorial (2 * n + 1) := by
        rw [h12]
        ring_nf
        <;> omega
      rw [h14, h13]
      have h15 : (2 * n + 3) * Nat.factorial (2 * n + 1) < (2 * n + 3) * (2 * n + 2) * Nat.factorial (2 * n + 1) := by
        have h16 : Nat.factorial (2 * n + 1) > 0 := by
          apply Nat.factorial_pos
        have h17 : (2 * n + 3) > 0 := by
          omega
        have h18 : (2 * n + 2) > 1 := by
          omega
        nlinarith [ show (0 : ℕ) < Nat.factorial (2 * n + 1) from Nat.factorial_pos (2 * n + 1), show (0 : ℕ) < (2 * n + 3) by omega ]
      exact h15
    have h16 : (Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2)) / Nat.factorial (2 * n + 3) = 0 := by
      rw [Nat.div_eq_zero_iff]
      all_goals
      omega
    exact h16
  have h2 : Tendsto (λ n => (Nat.factorial (2 * n + 1) + Nat.factorial (2 * n + 2)) / Nat.factorial (2 * n + 3)) atTop (𝓝 0) := by 
    simp_all [h1]
  exact_mod_cast h2