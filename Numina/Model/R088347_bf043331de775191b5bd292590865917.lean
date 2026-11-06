import Mathlib

theorem number_theory_238129 (g s : Fin 10 → ℕ) (h₀ : ∀ i, s i = 2 * g i)
    (h₁ : ∀ i j, i ≠ j → ¬(10 ∣ g i - g j)) :
    ¬∃ h : Fin 10 → ℕ, (∀ i, h i = 2 * g i) ∧
      (∀ i j, i ≠ j → ¬(10 ∣ h i - h j)) := by
  rintro ⟨h, ⟨h2, h3⟩⟩
  have h1' : ¬ (10 ∣ h 0 - h 1) := h3 0 1 (by simp)
  have h2' : ¬ (10 ∣ h 1 - h 0) := h3 1 0 (by simp)
  have h4 : (2 * g 0) % 10 = (2 * g 1) % 10 := by 
    omega
  have h5 : (g 0) % 5 = (g 1) % 5 := by 
    omega
  have h6 : 10 ∣ g 0 - g 1 := by
    omega
  have h7 : ¬ (10 ∣ g 0 - g 1) := h₁ 0 1 (by simp)
  contradiction