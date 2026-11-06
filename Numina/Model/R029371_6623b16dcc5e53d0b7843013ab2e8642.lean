import Mathlib

theorem algebra_604165 {f : ℝ → ℝ} : (∀ x y, f x * f y = f (x + y) + x * y) ↔
(∀ x, f x = -x + 1) ∨ (∀ x, f x = x + 1):= by
  constructor
  · -- Assume functional equation, prove the two possible solutions.
    intro h
    have h1 : ∃ a : ℝ, f a ≠ 0:= by
      by_contra H
      simp at H
      simp [H] at h
      specialize h 1 1
      simp at h
    rcases h1 with ⟨a, ha⟩
    have h1 : f 0 = 1:= by
      specialize h a 0
      simp at h
      replace h : f a * (f 0 - 1) = 0:= by linarith 
      simp [ha] at h
      linarith

    have h2 : f 1 = 0 ∨ f (-1) = 0:= by 
      specialize h 1 (-1)
      simp at h
      rw [h1] at h 
      simp at h 
      exact h
    rcases h2 with h2 | h2
    · -- Assume f(1) = 0, we need to prove f(x) = -x + 1
      left 
      intro x
      specialize h 1 (x - 1)
      simp at h 
      rw [h2] at h 
      simp at h 
      linarith
    · -- Assume f(-1) = 0, we need to prove f(x) = x + 1
      right 
      intro x
      specialize h (-1) (x + 1)
      simp at h 
      rw [h2] at h 
      simp at h 
      linarith
  · -- Reverse direction: prove both solutions satisfy the functional equation.
    intro h 
    rcases h with h | h
    · -- Assume f(x) =1 - x
      intro x y 
      simp [h x, h y, h (x + y)]
      <;> ring 
    · -- Assume f(x) = x +1
      intro x y 
      simp [h x, h y, h (x + y)]
      <;> ring