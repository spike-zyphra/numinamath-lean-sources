import Mathlib

theorem number_theory_11162 (n : ℕ) (h₀ : n > 1)
    (h₁ : (n.digits 285).length = 4) (h₂ : Odd (n.digits 285).head!) : n = 6 := by
  have h3 : n ≤ 285 := by
    by_contra h
    push_neg at h
    have h4 : (n.digits 285).length = 1 := by 
      simp [h]
      <;> omega 
    omega 
  interval_cases n <;> norm_num at h₁ h₂ ⊢
  <;> try { tauto }