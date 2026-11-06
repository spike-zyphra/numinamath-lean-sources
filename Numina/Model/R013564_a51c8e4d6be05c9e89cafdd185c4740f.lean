import Mathlib

theorem algebra_235820 (f : ℝ → ℝ) (h₀ : ∀ x > 0, f x > 0)
    (h₁ : f 1 = 1) (h₂ : ∀ a b, f (a + b) * (f a + f b) = 2 * f a * f b + a ^ 2 + b ^ 2) :
    f 2019 = 2019 := by
  have h4 : f 2 = 2 := by
    specialize h₂ 1 1
    norm_num [h₁] at h₂
    nlinarith
  have h5 : f 0 = 0 := by
    have h4' : f 2 = 2 := h4
    specialize h₂ 2 0
    norm_num [h4'] at h₂
    nlinarith [h₀ 2 (by norm_num), h₀ 1 (by norm_num), h₀ (0.5 : ℝ) (by norm_num)]
  have h6 : ∀ x : ℝ, f x = x := by
    intro x
    have eq1 := h₂ x 0
    simp [h5] at eq1
    have eq2 : (f x) ^ 2 = x ^ 2 := by
      nlinarith
    by_cases h : x > 0
    · -- x > 0
      have hx1 : f x > 0 := h₀ x h
      have hx2 : f x = x := by
        nlinarith [eq2, hx1]
      exact hx2
    by_cases h' : x = 0
    · -- x = 0
      rw [h']
      linarith [h5
      ]
    have h2 : x < 0 := by
      by_contra h
      push_neg at h
      have : x = 0 := by linarith
      tauto
    have h7 : x < 0 := h2
    have h8 : -x > 0 := by nlinarith
    have h9 : f (-x) > 0 := h₀ (-x) h8
    have eq3 := h₂ x (-x)
    have eq4 : f (x + (-x)) * (f x + f (-x)) = 2 * f x * f (-x) + x ^ 2 + (-x) ^ 2 := by
      simpa using eq3
    have eq5 : f (x + (-x)) = f 0 := by
      ring_nf
    rw [eq5, h5] at eq4
    have eq6 : f x * f (-x) = -x ^ 2 := by
      nlinarith
    have hx1 : f x < 0 := by
      nlinarith [eq6, h9, h7
      ]
    have hx2 : f x = x := by
      nlinarith [eq2, hx1
      ]
    exact hx2
  have h7 : f 2019 = 2019 := by
    specialize h6 2019
    linarith
  exact h7