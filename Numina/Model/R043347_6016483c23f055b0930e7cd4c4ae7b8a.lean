import Mathlib

theorem algebra_239956 (m b z : ℕ) (h₀ : b = 2 * m) (h₁ : z = 2 * b) (h₂ : z + m = b + 153) :
    m = 51 ∧ b = 102 ∧ z = 204 := by
  have h3 : z = 4 * m := by
    rw [h₁, h₀]
    all_goals omega
  have hm : m = 51 := by
    omega
  have hb : b = 102 := by
    rw [hm] at h₀
    omega
  have hz : z = 204 := by 
    rw [hm] at h3
    omega
  exact ⟨hm, hb, hz⟩