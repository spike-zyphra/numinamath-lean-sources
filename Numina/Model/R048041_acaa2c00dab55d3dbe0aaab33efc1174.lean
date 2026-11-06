import Mathlib

theorem number_theory_243021 (x y : ℕ) (h₀ : x + y = 2015) (h₁ : y = ⌊x / 10⌋₊) :
    x = 1832 ∧ y = 183 := by 
  have h2 : x ≤ 2015 := by 
    omega
  have h3 : y ≤ 2015 := by 
    omega
  have h4 : y = x / 10 := by
    norm_num at h₁
    omega
  have eq1 : x = 2015 - y := by 
    omega
  rw [eq1] at h4
  have h7 : y ≤ 2015 := by
    omega
  have h8 : x = 1832 := by 
    omega
  have h9 : y = 183 := by 
    omega
  exact ⟨h8, h9⟩