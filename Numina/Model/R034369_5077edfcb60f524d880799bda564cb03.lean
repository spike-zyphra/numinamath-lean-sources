import Mathlib

theorem algebra_81934 {R : Type*} [Ring R] (hR : ∀ a : R, a ^ 2 = 0) :
    ∀ a b c : R, a * b * c + a * b * c = 0 := by
  have h1 : (1 : R) = 0 := by
    have h11 := hR 1
    simp at h11
    exact h11
  have h2 : ∀ a : R, a = 0 := by
    intro a
    calc
      a = a * (1 : R) := by simp
      _ = a * (0 : R) := by rw [h1]
      _ = (0 : R) := by simp
  intro a b c
  simp [h2 a, h2 b, h2 c]