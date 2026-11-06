import Mathlib

theorem algebra_196435 {f g : ℝ → ℝ} (hf : ∀ x, f (x + 1) = (x + 1) * f x) (f_ne_zero : ∀ x, f x ≠ 0) :
    (∀ x, f (x + 1) * g (x + 1) = (x + 1) * f x * g x) ↔ Function.Periodic g 1 := by
  constructor
  · -- Assume that ∀ x, f (x + 1) * g (x + 1) = (x + 1) * f x * g x, prove Function.Periodic g 1
    intro h
    unfold Function.Periodic
    intro x
    have eq1 : f (x + 1) = (x + 1) * f x := hf x
    have eq2 := h x
    rw [eq1] at eq2
    by_cases h1 : x + 1 = 0
    · -- x + 1 = 0, so x = -1
      have h2 : x = -1 := by linarith
      rw [h2] at eq2
      have h4 : f 0 = 0 := by
        specialize hf (-1)
        norm_num at hf
        all_goals
          linarith
      have h5 : f 0 ≠ 0 := f_ne_zero 0
      contradiction
    · -- x + 1 ≠ 0
      have eq3 : f x ≠ 0 := f_ne_zero x
      have eq4 : (x + 1 : ℝ) ≠ 0 := by
        by_contra h_eq
        have : x + 1 = 0 := by linarith
        contradiction
      have eq5 : (x + 1 : ℝ) * f x * (g (x + 1) - g x) = 0 := by
        linarith
      have eq6 : g (x + 1) - g x = 0 := by
        apply (mul_left_inj' eq3).mp
        apply (mul_left_inj' eq4).mp
        linarith
      linarith
  · -- Assume Function.Periodic g 1, prove ∀ x, f (x + 1) * g (x + 1) = (x + 1) * f x * g x
    intro hg
    intro x
    have eq1 : f (x + 1) = (x + 1) * f x := hf x
    have eq2 : g (x + 1) = g x := by
      unfold Function.Periodic at hg
      specialize hg x
      simpa using hg
    calc
      f (x + 1) * g (x + 1)
          = f (x + 1) * g x := by
            rw [eq2]
      _ = (x + 1) * f x * g x := by
        rw [eq1]
        all_goals ring