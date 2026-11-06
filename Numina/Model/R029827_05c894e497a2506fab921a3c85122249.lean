import Mathlib

theorem number_theory_50110 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : (a + b) ∣ (5 * a + 3 * b)) : a = b := by 
  have h2 : a + b > 0 := by
    omega
  rcases h₁ with ⟨k, hk⟩
  have eq1 : 5 * a + 3 * b = k * (a + b) := by
    linarith
  have h4 : k > 0 := by
    by_contra h
    simp [h] at eq1
    have h_eq : 5 * a + 3 * b > 0 := by 
      omega
    have h_eq2 : k = 0 := by 
      omega 
    rw [h_eq2] at eq1 
    simp at eq1 
    omega 
  have h5 : k ≤ 5 := by
    by_contra h
    have h_eq : k ≥ 6 := by 
      omega 
    nlinarith [show a ≥ 1 by omega, show b ≥ 1 by omega]
  interval_cases k <;> omega