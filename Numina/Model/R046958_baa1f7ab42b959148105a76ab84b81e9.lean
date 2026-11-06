import Mathlib

theorem algebra_168959 (f : ℝ → ℝ → ℝ) (h₀ : ∀ x, f x x = 0)
    (h₁ : ∀ x y z, f x (f y z) = f x y + z) :
    f 1993 1935 = 58 := by

  -- First proving $f \ x \ 0 = x$
  have h2 : ∀ x, f x 0 = x := by
    intro x
    have eq1 := h₁ x x x
    have eq2 : f x x = 0 := h₀ x
    simp [eq2] at eq1
    linarith

  -- Prove that f x y = x - y, using previous result $f \ x \ 0 = x$.
  have h3 : ∀ x y, f x y = x - y := by
    intro x y
    have eq1 := h₁ x y y
    have eq2 : f y y = 0 := h₀ y
    have eq3 : f x (f y y) = f x y + y := by simpa using eq1
    rw [eq2] at eq3
    have eq4 : f x 0 = x := h2 x
    linarith [eq4, eq3]

  -- Now, apply the formula to compute f 1993 1935.
  -- Set x = 1993, y = 1935.
  -- So f 1993 1935 = 1993 - 1935 = 58.
  specialize h3 1993 1935
  rw [h3]
  norm_num