import Mathlib
theorem algebra_20995 (m : ℝ) :
    (∃ x, x ≠ 1 ∧ (3 * x ^ 2 - 4 * x + 1) / (x - 1) = m) →  m ≠ 2 := by 
  intro h
  rcases h with ⟨x, hx1, heq⟩
  by_contra h2
  have eq2 : (3 * x ^ 2 - 4 * x + 1) / (x - 1) = 2 := by
    rw [heq]
    all_goals linarith
  have hx2 : x - 1 ≠ 0 := by
    intro h'
    apply hx1
    linarith
  have eq3 : 3 * x ^ 2 - 4 * x + 1 = 2 * (x - 1) := by
    have h : (3 * x ^ 2 - 4 * x + 1) / (x - 1) = 2 := eq2
    have : x - 1 ≠ 0 := hx2
    field_simp [hx2] at h ⊢
    all_goals linarith
  have eq4 : 3 * (x - 1) ^ 2 = 0 := by
    nlinarith 
  have eq5 : (x - 1) ^ 2 = 0 := by
    linarith 
  have eq6 : x - 1 = 0 := by 
    apply pow_eq_zero 
    exact eq5
  have eq7 : x = 1 := by 
    linarith 
  tauto