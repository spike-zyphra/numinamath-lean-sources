import Mathlib

theorem algebra_213207 (p : ℝ → ℝ) (hp : ∃ a b c d, p = fun x => a*x^3 + b*x^2 + c*x + d)
    (h₀ : p (-6) = 30) (h₁ : p (-3) = 45) (h₂ : p (-1) = 15) (h₃ : p 2 = 30)
    (h₄ : ∀ x ∈ Set.Icc (-6) 2, p x > 0) :
    ∫ x in (-6)..2, max (p x) 0 = 240 := by
  rcases hp with ⟨a, b, c, d, hp'⟩
  have eq1 : a * (-6)^3 + b * (-6)^2 + c * (-6) + d = 30 := by
    rw [hp'] at h₀
    norm_num at h₀ ⊢
    linarith
  have eq2 : a * (-3)^3 + b * (-3)^2 + c * (-3) + d = 45 := by
    rw [hp'] at h₁
    norm_num at h₁ ⊢
    linarith
  have eq3 : a * (-1)^3 + b * (-1)^2 + c * (-1) + d = 15 := by
    rw [hp'] at h₂
    norm_num at h₂ ⊢
    linarith
  have eq4 : a * (2)^3 + b * (2)^2 + c * (2) + d = 30 := by
    rw [hp'] at h₃
    norm_num at h₃ ⊢
    linarith
  have ha : a = 1 := by
    ring_nf at eq1 eq2 eq3 eq4
    nlinarith
  have hb : b = 6 := by
    ring_nf at eq1 eq2 eq3 eq4
    nlinarith
  have hc : c = -4 := by
    ring_nf at eq1 eq2 eq3 eq4
    nlinarith
  have hd : d = 6 := by
    ring_nf at eq1 eq2 eq3 eq4
    nlinarith
  have heq2 : p = fun x => x^3 + 6*x^2 - 4*x + 6 := by
    funext x
    rw [hp']
    simp [ha, hb, hc, hd]
    all_goals ring
  have eq5 : ∫ x in (-6)..2, max (p x) 0 = ∫ x in (-6)..2, p x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have h100 : p x > 0 := h₄ x (by
      simp at hx ⊢
      all_goals
      try { tauto }
      all_goals
      try { norm_num at hx ⊢; tauto }
    )
    have eq50 : max (p x) 0 = p x := by
      apply max_eq_left
      linarith
    simpa using eq50
  rw [eq5]
  rw [heq2]
  norm_num [intervalIntegral.integral_const, mul_add, mul_comm]