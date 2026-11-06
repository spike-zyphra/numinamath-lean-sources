import Mathlib

theorem algebra_4712 (f : ℕ → ℕ) (fmapsto : ∀ n ≠ 0, f n ≠ 0) :
    (∀ n ≠ 0, f (f (f n)) + f (f n) + f n = 3 * n) ∧ (∀ n ≠ 0, 3 * f (f (f n)) + 2 * f (f n) + f n = 6 * n) → ∀ n ≠ 0, f n = n := by
  rintro ⟨h₁, h₂⟩ 
  intro n hn
  have eq1 := h₁ n hn 
  have eq2 := h₂ n hn 
  have eq3 : ∀ n ≠ 0, f (f n) + 2 * f n = 3 * n := by
    intro n hn 
    have h₁n := h₁ n hn 
    have h₂n := h₂ n hn 
    omega 
  have eq4 := eq3 n hn 
  have eq5 : ∀ n ≠ 0, f n = n := by 
    intro n hn 
    have h₁n := h₁ n hn 
    have h₂n := h₂ n hn
    have eq4n := eq3 n hn 
    have h₃ := eq3 (f n) (show f n ≠ 0 by apply fmapsto n hn)
    omega 
  apply eq5 n hn 
  all_goals tauto
  all_goals omega