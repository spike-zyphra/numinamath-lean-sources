import Mathlib

theorem number_theory_23114 {n : ℕ} (hn : n ≠ 0) (h : 39500 / n = 123 ∧ 39500 % n = 17) :
    n = 321 := by
  have h₁ : 39500 = 123 * n + 17 := by
    have h2 := Nat.div_add_mod 39500 n
    rw [h.1, h.2] at h2
    linarith
  have h2 : n = 321 := by 
    omega
  exact h2