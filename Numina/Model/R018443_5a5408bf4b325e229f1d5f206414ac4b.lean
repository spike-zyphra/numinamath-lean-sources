import Mathlib

theorem number_theory_236797 (n : ℕ) (h₀ : n < 10000) (h₁ : n > 999)
    (h₂ : n / (n % 1000) = 3 ∧ n % (n % 1000) = 8) :
    n = 1496 ∨ n = 2996 := by
  rcases h₂ with ⟨h3, h4⟩
  have h5 : n % (n % 1000) = 8 := h4
  have h6 : n / (n % 1000) = 3 := h3
  have h7 : n % 1000 > 0 := by
    by_contra h
    have h8 : n % 1000 = 0 := by omega
    rw [h8] at h6 h5
    all_goals omega
  have h8 : n % 1000 ≤ 999 := by
    omega
  have h9 : n = 3 * (n % 1000) + 8 := by
    have h10 : n % (n % 1000) = 8 := h4
    have h11 : n / (n % 1000) = 3 := h3
    have h12 : n % 1000 > 0 := h7
    have h13 : n % 1000 ≤ 999 := h8
    have h14 : n = (n % 1000) * (n / (n % 1000)) + n % (n % 1000) := by
      rw [Nat.div_add_mod n (n % 1000)]
    rw [h3, h4] at h14
    nlinarith
  interval_cases h : n % 1000 <;> try { 
    omega 
  }