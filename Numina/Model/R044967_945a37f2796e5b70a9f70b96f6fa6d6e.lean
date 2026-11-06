import Mathlib

theorem algebra_182056 {f : ℝ → ℝ} (m n : ℝ) (hmn : m ≠ n)
    (h₁ : ∀ x, f (m + x) = f (m - x)) (h₂ : ∀ x, f (n + x) = f (n - x)) :
    ∃ c, c ≠ 0 ∧ Function.Periodic f c := by
  use 2 * (n - m)
  constructor
  · -- Show that 2 * (n - m) ≠ 0
    by_contra h
    have : n - m = 0 := by linarith
    have h_eq : n = m := by linarith
    tauto
  · -- Show that f is periodic with period 2 * (n - m).
    unfold Function.Periodic
    intro x
    have h5 : f (x) = f (2 * m - x) := by
      have h6 := h₁ (x - m)
      rw [show m + (x - m) = x by linarith, show m - (x - m) = 2 * m - x by linarith] at h6
      linarith
    have eq2 : f (x + 2 * (n - m)) = f (x) := by
      have eq3 : f (x + 2 * (n - m)) = f (2 * m - x) := by
        have eq4 : f (2 * m - x) = f (2 * n - (2 * m - x)) := by
          have eq5 := h₂ ((2 * m - x) - n)
          rw [show n + ((2 * m - x) - n) = (2 * m - x) by linarith, 
              show n - ((2 * m - x) - n) = 2 * n - (2 * m - x) by linarith] at eq5
          linarith
        have eq6 : 2 * n - (2 * m - x) = x + 2 * (n - m) := by
          linarith
        rw [eq6] at eq4
        linarith [eq4, h5]
      linarith [eq3, h5]
    linarith [eq2]