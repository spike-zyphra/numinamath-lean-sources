import Mathlib

theorem algebra_117298 {x y : ℕ} (h₀ : x + y = 2016) (h₁ : (x / 4 : ℤ) - (y / 4 : ℤ) = 468) :
    x = 1944 ∧ y = 72 := by 
  have h2 : (x : ℤ) + (y : ℤ) = 2016 := by
    exact_mod_cast h₀
  have h3 : (x : ℤ) - (y : ℤ) = 1872 := by
    omega
  have h4 : (x : ℤ) = 1944 := by
    omega
  have h5 : (y : ℤ) = 72 := by
    omega
  have h6 : x = 1944 := by
    exact_mod_cast h4
  have h7 : y = 72 := by
    exact_mod_cast h5
  exact ⟨h6, h7⟩