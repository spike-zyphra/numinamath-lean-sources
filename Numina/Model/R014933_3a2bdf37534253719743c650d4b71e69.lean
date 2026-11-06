import Mathlib

theorem algebra_129324 {f : ℝ → ℝ} (h : ∀ x y, f (2 * f x + f y) = 2 * x + f y) :
    ∀ x, f x = x := by
  have h1 : ∀ x y, f x = f y → x = y := by
    intro x y h_eq
    have eq1 := h x 0
    have eq2 := h y 0
    have eq3 : f (2 * f x + f 0) = 2 * x + f 0 := by
      simpa using eq1
    have eq4 : f (2 * f y + f 0) = 2 * y + f 0 := by
      simpa using eq2
    have eq5 : 2 * f x + f 0 = 2 * f y + f 0 := by
      have eq6 : f x = f y := h_eq
      linarith [eq6]
    have eq6 : f (2 * f x + f 0) = f (2 * f y + f 0) := by
      rw [show 2 * f x + f 0 = 2 * f y + f 0 by linarith [eq5]]
    have eq7 : 2 * x + f 0 = 2 * y + f 0 := by
      linarith [eq3, eq4, eq6]
    linarith
  have h4 : f 0 = 0 := by
    have h5 : ∀ y, f (2 * f 0 + f y) = f y := by 
      intro y
      specialize h 0 y
      norm_num at h ⊢
      all_goals linarith
    have h5' := h5 0
    have eq1 : f (2 * f 0 + f 0) = f 0 := by
      simpa using h5'
    have eq2 : 2 * f 0 + f 0 = (0 : ℝ) := by
      have h_inj := h1 (2 * f 0 + f 0) 0 (by
        simpa using eq1
      )
      linarith [h_inj, eq1]
    linarith
  have h3 : ∀ y, f (f y) = f y := by
    intro y
    have eq1 : f (2 * f 0 + f y) = 2 * (0 : ℝ) + f y := by 
      specialize h 0 y
      simpa using h
    rw [h4] at eq1
    norm_num at eq1 ⊢
    all_goals linarith [eq1]
  have h9 : ∀ x, f (2 * f x) = 2 * x := by 
    intro x
    specialize h x 0
    rw [h4] at h
    norm_num at h ⊢
    all_goals linarith [h]
  intro x
  have eq3 : f (2 * f x) = 2 * x := h9 x
  have eq5 : f (2 * f (f x)) = 2 * (f x) := by 
    apply h9 
  have eq6 : f (2 * f (f x)) = f (2 * f x) := by 
    have eq7 : f (f x) = f x := h3 x
    rw [show 2 * f (f x) = 2 * f x by
      have eq8 : f (f x) = f x := h3 x
      linarith [eq8]
    ]
  have eq8 : f (2 * f x) = 2 * (f x) := by
    linarith [eq6, eq5]
  linarith [eq3, eq8]