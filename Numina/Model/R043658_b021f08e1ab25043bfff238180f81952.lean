import Mathlib

theorem algebra_152 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a^2 + b^2 + c^2 = 1) (h₂ : a * b * c ≠ 0) :
(a^5 + b^5 + c^5) / (a * b * c) = 5 / 2 := by
  have h3 : c = -a - b := by linarith 
  have h4 : a ^ 2 + b ^ 2 + (-a - b) ^ 2 = 1 := by 
    rw [show c = -a - b by linarith [h₀]] at h₁ 
    linarith 
  have h5 : a ^ 2 + b ^ 2 + a * b = 1 / 2 := by 
    nlinarith 
  have eq1 : a ^ 5 + b ^ 5 + c ^ 5 = -5 / 2 * (a * b * (a + b)) := by 
    rw [show c = -a - b by linarith [h₀]]
    have eq2 : a ^ 5 + b ^ 5 + (-a - b) ^ 5 = -5 * (a * b * (a + b)) * (a ^ 2 + b ^ 2 + a * b) := by 
      ring_nf 
    rw [eq2]
    rw [show a ^ 2 + b ^ 2 + a * b = 1 / 2 by linarith [h5]]
    all_goals ring_nf 
  have eq3 : a * b * c = - (a * b * (a + b)) := by 
    rw [show c = -a - b by linarith [h₀]]
    ring 
  have eq4 : (a ^ 5 + b ^ 5 + c ^ 5) / (a * b * c) = 5 / 2 := by 
    rw [eq1, eq3]
    have h₃ : a * b * (a + b) ≠ 0 := by
      by_contra h
      have : a * b * c = 0 := by 
        rw [eq3]
        linarith [h]
      contradiction 
    field_simp [h₃] 
    <;> ring_nf
    <;> linarith 
  exact eq4