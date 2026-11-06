import Mathlib

open Function

theorem algebra_10288 {f g : ℝ → ℝ} (hf : f = fun x => x + 2) (hg : g = fun x => x / 3) :
    f (invFun g (invFun f (invFun f (g (f 19))))) = 11 := by

  have hf1 : ∀ x, f x = x + 2 := by
    intro x
    rw [hf]

  have hg1 : ∀ x, g x = x / 3 := by
    intro x
    rw [hg]

  have h1 : invFun f = fun y => y - 2 := by
    funext y
    have h2 : ∀ x : ℝ, f x = y ↔ x = y - 2 := by
      intro x
      constructor
      · -- Assume f x = y, need to prove x = y - 2
        intro hfx
        rw [hf1 x] at hfx
        linarith
      · -- Assume x = y - 2, need to prove f x = y
        intro hxy
        rw [hf1 x, hxy]
        linarith
    simp [Function.invFun, h2]

  have h2 : invFun g = fun y => 3 * y := by
    funext y
    have h3 : ∀ x : ℝ, g x = y ↔ x = 3 * y := by
      intro x
      constructor
      · -- Assume g x = y, need to prove x = 3 * y
        intro hgx
        rw [hg1 x] at hgx
        linarith
      · -- Assume x = 3 * y, need to prove g x = y
        intro hxy
        rw [hg1 x, hxy]
        linarith
    simp [Function.invFun, h3]

  have h3 : f 19 = (21 : ℝ) := by
    rw [hf1]
    norm_num

  have h4 : g (f 19) = (7 : ℝ) := by
    rw [h3, hg1]
    norm_num

  have h5 : invFun f (g (f 19)) = (5 : ℝ) := by
    rw [h4, h1]
    all_goals norm_num

  have h6 : invFun f (invFun f (g (f 19))) = (3 : ℝ) := by
    rw [h5, h1]
    all_goals norm_num

  have h7 : invFun g (invFun f (invFun f (g (f 19)))) = (9 : ℝ) := by
    rw [h6, h2]
    all_goals norm_num

  rw [h7, hf1]
  all_goals norm_num