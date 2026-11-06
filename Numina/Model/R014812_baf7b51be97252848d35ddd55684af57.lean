import Mathlib

open Nat


lemma lemma_1 (n : ℕ) : (n + 3) ∣ (n * (n + 1) * (n + 2) + 6) := by
  use n ^ 2 + 2
  cases n with
  | zero =>
    simp
  | succ n =>
    simp [Nat.add_comm] at *
    <;> ring_nf
    <;> omega


theorem number_theory_159872 (n : ℕ) (h : n > 0) :
    (n + 3) ∣ n * (n + 1) * (n + 2) ↔ n + 3 = 6 := by
  constructor
  · -- Forward implication: if (n + 3) divides n * (n + 1) * (n + 2), then n + 3 = 6
    intro hdiv
    have h1 : (n + 3) ∣ 6 := by
      have h2 : (n + 3) ∣ (n * (n + 1) * (n + 2) + 6) := lemma_1 n
      have h3 : (n + 3) ∣ (n * (n + 1) * (n + 2) + 6 - (n * (n + 1) * (n + 2))) := by
        apply Nat.dvd_sub'
        · exact h2
        · exact hdiv
      have h4 : n * (n + 1) * (n + 2) + 6 - (n * (n + 1) * (n + 2)) = 6 := by
        omega
      rw [h4] at h3
      exact h3
    have h3 : (n + 3) ≤ 6 := by
      exact Nat.le_of_dvd (by norm_num) h1
    interval_cases h4 : (n + 3) <;> try simp at h1 h4 ⊢ <;> all_goals omega
  · -- Backward implication: n + 3 = 6 implies (n + 3) ∣ n * (n + 1) * (n + 2)
    intro h_eq
    have hn3 : n = 3 := by
      omega
    rw [hn3]
    all_goals norm_num