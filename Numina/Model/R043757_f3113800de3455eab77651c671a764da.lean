import Mathlib

theorem algebra_145949 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h : ∀ x, f x + f (x + a) + f x * f (x + a) = 1) :
    ∃ c > 0, Function.Periodic f c := by
  use 2 * a
  constructor
  · -- Show that c > 0
    nlinarith
  · -- Show that f is 2a-periodic
    unfold Function.Periodic
    intro x 
    have eq1 : f x + f (x + a) + f x * f (x + a) = 1 := by
      specialize h x 
      simpa using h
    have eq2 : f (x + a) + f (x + 2 * a) + f (x + a) * f (x + 2 * a) = 1 := by 
      specialize h (x + a)
      rw [show x + a + a = x + 2 * a by ring] at h
      linarith
    have eq3 : f (x + 2 * a) = f x := by
      have h1 : 1 + f (x + a) ≠ 0 := by
        by_contra h1
        have h1' : f (x + a) = -1 := by linarith
        rw [h1'] at eq1
        nlinarith 
      have h2 : 1 + f x ≠ 0 := by 
        by_contra h2 
        have h2' : f x = -1 := by linarith 
        rw [h2'] at eq1 
        nlinarith
      have hx1 : f (x + a) = (1 - f x) / (1 + f x) := by
        field_simp [h2] at *
        nlinarith 
      have hx2 : f (x + 2 * a) = (1 - f (x + a)) / (1 + f (x + a)) := by 
        field_simp [h1] at *
        nlinarith 
      rw [hx2]
      rw [hx1]
      field_simp [h2]
      <;> nlinarith
    linarith [eq3]