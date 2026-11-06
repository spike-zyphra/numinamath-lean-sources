import Mathlib

theorem algebra_17113 {p q : ℝ} (hp : 1 < p) (hq : p < q)
    (h₁ : 1 / p + 1 / q = 1) (h₂ : p * q = 9 / 2) : q = 3 := by

  have h3 : p ≠ 0 := by linarith
  have h4 : q ≠ 0 := by
      by_contra h
      rw [h] at h₁ 
      field_simp [h3] at h₁ 
      all_goals linarith

  have h₃ : p + q = p * q := by
    field_simp [h3, h4] at h₁
    nlinarith

  have h₄ : p + q = 9 / 2 := by
    nlinarith [h₂, h₃]

  have h₅ : p ^ 2 - 9 / 2 * p + 9 / 2 = 0 := by 
    nlinarith [h₃, h₂]

  have hquadratic : (p - 3 / 2) * (p - 3) = 0 := by 
    nlinarith [h₅]

  cases' (mul_eq_zero.1 hquadratic) with hp1 hp2
  
  · -- $p - 3/2 = 0$
    have hp' : p = 3 / 2 := by linarith 
    have hq' : q = 3 := by 
      nlinarith [h₂, hp']
    linarith

  · -- $p - 3 = 0$
    have hp' : p = 3 := by linarith 
    have hq' : q = 3 / 2 := by 
      nlinarith [h₂, hp']
    linarith