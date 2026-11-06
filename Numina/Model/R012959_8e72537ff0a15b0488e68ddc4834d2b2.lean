import Mathlib

theorem algebra_287530 {f : ℝ → ℝ} (h : ∀ x y, y ≠ 0 → f (x + y) = f (x * y - x / y))
    (hf : ∃ c, Function.Periodic f c) :
    ∃ c, Function.Periodic f c ∧ c > 0 ∧ c = (1 + Real.sqrt 5) / 2 := by
  have h1 : ∀ (y : ℝ), y ≠ 0 → f y = f 0 := by
    intro y hy
    specialize h 0 y hy
    simp at h
    simpa using h
  rcases hf with ⟨c, hc⟩
  use (1 + Real.sqrt 5) / 2
  constructor
  · -- Show that (1 + sqrt 5) / 2 is a period of f
    intro x
    have h3 : ∀ (x : ℝ), f x = f 0 := by
      intro x
      by_cases h' : x = 0
      · -- x = 0
        rw [h']
      · -- x ≠ 0
        have hx : x ≠ 0 := by
          intro h
          apply h'
          linarith
        specialize h1 x hx
        linarith
    have eq1 : f (x + (1 + Real.sqrt 5) / 2) = f x := by
      have eq1 : f (x + (1 + Real.sqrt 5) / 2) = f 0 := by
        apply h3
      have eq2 : f x = f 0 := by
        apply h3
      linarith
    simpa using eq1
  constructor
  · -- Show that (1 + sqrt 5) / 2 > 0
    have h3 : Real.sqrt 5 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Show that (1 + sqrt 5) / 2 = (1 + Real.sqrt 5) / 2
    rfl