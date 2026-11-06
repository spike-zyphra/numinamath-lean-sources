import Mathlib

theorem algebra_131556 (f : ℝ → ℝ) (h₀ : Function.Injective f)
    (h₁ : ∀ x y, f (f x + y) = f (x + y) + f 2012) :
    False := by
  have eq1 : ∀ x, f (f x) = f x + f 2012 := by
    intro x
    specialize h₁ x 0
    simp at h₁
    linarith
  have eq2 : ∀ y, f (f 0 + y) = f y + f 2012 := by
    intro y
    specialize h₁ 0 y
    norm_num at h₁
    all_goals try linarith
  have eq3 : ∀ x, f (f 0 + x) = f (f x) := by
    intro x
    have eq2_x : f (f 0 + x) = f x + f 2012 := eq2 x
    have eq1_x : f (f x) = f x + f 2012 := eq1 x
    linarith [eq2_x, eq1_x]
  have eq4 : ∀ x, f 0 + x = f x := by
    intro x
    have injective_eq : f (f 0 + x) = f (f x) := eq3 x
    have eq5 : f 0 + x = f x := by
      apply h₀ at injective_eq
      linarith
    linarith
  have eq6 : f 2012 = f 0 + (2012 : ℝ) := by
    specialize eq4 2012
    linarith
  have eq7 : ∀ x, f x = f 0 + x := by
    intro x
    specialize eq4 x
    linarith
  have eq8 : ∀ x y, f (f x + y) = f (x + y) + f 2012 := by
    intro x y
    specialize h₁ x y
    simpa using h₁
  have eq9 : ∀ x y, 2 * f 0 + x + y = 2 * f 0 + x + y + 2012 := by
    intro x y
    have h2 : f (f x + y) = f (x + y) + f 2012 := h₁ x y
    have eq11 : f (f x + y) = 2 * f 0 + x + y := by
      calc
        f (f x + y) = f 0 + (f x + y) := by
          rw [eq7 (f x + y)]
        _ = f 0 + (f 0 + x + y) := by
          have h10 : f x = f 0 + x := by
            apply eq7
          rw [h10]
          all_goals ring
        _ = 2 * f 0 + x + y := by ring
    have eq12 : f (x + y) + f 2012 = 2 * f 0 + x + y + 2012 := by
      have eq13 : f (x + y) = f 0 + (x + y) := by
        apply eq7
      have eq14 : f 2012 = f 0 + 2012 := by
        specialize eq7 2012
        linarith
      rw [eq13, eq14]
      all_goals ring
    linarith [h2, eq11, eq12]
  specialize eq9 0 0
  linarith