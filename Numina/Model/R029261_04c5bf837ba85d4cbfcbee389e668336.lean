import Mathlib

theorem number_theory_161491 (x y z : ℕ) (h₀ : 3 * x + 4 * y + 5 * z = 30) (h₁ : (x + y + z).Prime) :
    (x, y, z) = (0, 5, 2) ∨ (x, y, z) = (1, 3, 3) ∨ (x, y, z) = (2, 1, 4) := by
  have h2 : x ≤ 10 := by 
    omega
  have h3 : y ≤ 7 := by 
    omega
  have h4 : z ≤ 6 := by 
    omega
  have h5 : x ≤ 10 := h2
  have h6 : y ≤ 7 := h3
  have h7 : z ≤ 6 := h4
  interval_cases x <;> interval_cases y
  <;> interval_cases z
  <;> norm_num at h₀ h₁ ⊢
  <;> tauto