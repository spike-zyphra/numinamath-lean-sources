import Mathlib

theorem number_theory_15144 (total_chips : ℕ) (h₀ : total_chips = 54)
    (smaller : ℕ) (lager : ℕ) (h₁ : smaller + lager = total_chips)
    (h₂ : ∃ p : ℕ, p.Prime ∧ smaller = lager + p) :
    lager ≤ 26 := by 
  rw [h₀] at h₁
  rcases h₂ with ⟨p, hp_prime, h3⟩
  have eq1 : smaller = lager + p := h3
  rw [eq1] at h₁
  have h7 : p ≥ 2 := by 
    apply Nat.Prime.two_le hp_prime
  linarith