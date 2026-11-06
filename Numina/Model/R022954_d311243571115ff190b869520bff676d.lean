import Mathlib

theorem number_theory_278717 : ∀ N : ℕ, ∃ n : ℕ, n > N ∧ 5 ∣ 4 * n^2 + 1 ∧ 13 ∣ 4 * n^2 + 1 := by 
  intro N 
  use 65 * (N + 1) + 56 
  constructor 
  · -- Show that n > N
    nlinarith 
  constructor 
  · -- Show that 5 ∣ 4 * n^2 + 1 
    have h1 : (5 ∣ 4 * (65 * (N + 1) + 56)^2 + 1) := by 
      ring_nf 
      omega 
    exact h1 
  · -- Show that 13 ∣ 4 * n^2 + 1 
    have h2 : (13 ∣ 4 * (65 * (N + 1) + 56)^2 + 1) := by 
      ring_nf 
      omega 
    exact h2