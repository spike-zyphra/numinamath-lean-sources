import Mathlib

theorem number_theory_288348 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ p : ℕ, p = 91 * n ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p))
    (h₃ : ∃ p : ℕ, p = 93 * n ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p))
    (h₄ : ∃ p : ℕ, p = 95 * n ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p))
    (h₅ : ∃ p : ℕ, p = 97 * n ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p)) :
    n = 55 := by
  rcases h₂ with ⟨p2, hp2_eq, hp2_pal⟩
  rcases h₃ with ⟨p3, hp3_eq, hp3_pal⟩
  rcases h₄ with ⟨p4, hp4_eq, hp4_pal⟩
  rcases h₅ with ⟨p5, hp5_eq, hp5_pal⟩
  interval_cases n <;> norm_num [hp2_eq] at hp2_pal
    <;> norm_num [hp3_eq] at hp3_pal
    <;> norm_num [hp4_eq] at hp4_pal
    <;> norm_num [hp5_eq] at hp5_pal
    <;> all_goals native_decide