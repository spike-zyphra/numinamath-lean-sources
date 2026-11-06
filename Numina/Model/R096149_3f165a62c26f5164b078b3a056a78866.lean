import Mathlib

theorem algebra_158230 {k l : ℤ} {P : Polynomial ℤ} (hP : P.degree > 0)
    (hk : ∀ x ∈ P.roots, k * x ∈ P.roots) (hl : ∀ x ∈ P.roots, l * x ∈ P.roots) :
    ∀ x ∈ P.roots, k * l * x ∈ P.roots := by 
  intro x hx
  have hk_x : k * x ∈ P.roots := hk x hx
  have hl_kx : l * (k * x) ∈ P.roots := hl (k * x) hk_x
  have h_comm : k * l * x = l * (k * x) := by 
    ring
  rw [h_comm]
  exact hl_kx