import Mathlib

theorem number_theory_127802 {q p : ℕ} (hp : Odd p ∧ p ≠ 5) :
    Even (Nat.floor (10 ^ (q / p) * (q / p : ℝ))) →
    (Nat.floor (10 ^ (q / p) * (q / p : ℝ)) / (q / p)) = 45 / 100 ∧
    Odd (Nat.floor (10 ^ (q / p) * (q / p : ℝ))) →
    (Nat.floor (10 ^ (q / p) * (q / p : ℝ)) / (q / p)) ≠ 45 / 100 := by 
  intro heven h
  have h1 : (Nat.floor (10 ^ (q / p) * (q / p : ℝ)) / (q / p)) = 45 / 100 := h.1
  have h2 : Odd (Nat.floor (10 ^ (q / p) * (q / p : ℝ))) := h.2
  obtain ⟨k, hk⟩ := heven
  obtain ⟨m, hm⟩ := h2
  omega