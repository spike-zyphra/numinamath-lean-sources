import Mathlib

theorem other_91837 {f g : ℝ → ℝ} (hfg : ∀ x y, f (f (x + y)) = x * f y + g x) :
    ∃ k, ∀ x, (f x, g x) = (k, k * (1 - x)) := by
  have h1 : ∀ y, f (f y) = g 0 := by
    intro y
    specialize hfg 0 y
    norm_num at hfg
    simpa using hfg

  have h2 : ∀ x, f (f x) = x * f 0 + g x := by
    intro x
    specialize hfg x 0
    simp at hfg
    linarith

  have h3 : ∀ x, g x = g 0 - x * f 0 := by
    intro x
    have h4 : f (f x) = g 0 := h1 x
    have h5 : f (f x) = x * f 0 + g x := h2 x
    linarith [h4, h5]

  use f 0

  intro x

  have h6 : ∀ z, f z = f 0 := by
    intro z
    have eq1 := hfg (-z) z
    simp at eq1
    have eq3 : g (-z) = g 0 - (-z) * f 0 := h3 (-z)
    rw [eq3] at eq1
    have h8 : f (f 0) = g 0 := h1 0
    rw [h8] at eq1
    have h9 : z * (f 0 - f z) = 0 := by
      linarith [eq1]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · 
      rw [h10]
      all_goals simp
    · 
      linarith
  
  have hx1 : f x = f 0 := h6 x
  
  have h41 : g x = f 0 * (1 - x) := by
    have h42 : g x = g 0 - x * f 0 := h3 x
    have h44 : g 0 = f 0 := by 
      have eq1 : f (f 0) = g 0 := h1 0
      have eq2 : f (f 0) = f 0 := by 
        have h42 : f 0 = f 0 := by rfl
        have eq2 : f (f 0) = f 0 := by 
          apply h6 
        linarith [eq2]
      linarith [eq1, eq2]
    rw [h44] at h42
    linarith

  simp [hx1, h41]