import Mathlib

theorem number_theory_156421 {x y : ℕ} (h₀ : x + y = 2016) (h₁ : x / 10 = y) :
    x = 1833 ∧ y = 183 := by
  have h2 : x = 10 * y + (x % 10) := by
    omega
  have h3 : 11 * y + (x % 10) = 2016 := by
    omega
  have h4 : x % 10 < 10 := by 
    omega
  have h5 : y ≤ 183 := by 
    omega
  have h6 : y ≥ 183 := by 
    omega
  have hy : y = 183 := by 
    omega
  have hx : x = 1833 := by 
    omega
  exact ⟨hx, hy⟩