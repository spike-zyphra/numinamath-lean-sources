import Mathlib

theorem algebra_165376 (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔ f = fun x => (1 / 2) - x := by 
  constructor
  · -- First, the forward direction: if f satisfies the functional equation, then f(x) = 1/2 - x
    intro h
    have h1 : ∀ y, f 0 = 1 - f y - y := by
      intro y
      specialize h (f y) y
      simp at h
      linarith
    have h2 : f 0 = 1 / 2 := by
      have h3 : f 0 = 1 - f 0 := by
        specialize h1 0
        norm_num at h1
        linarith
      linarith
    funext x
    have h4 : f x = (1 / 2) - x := by
      have h5 : f 0 = 1 - f x - x := by
        specialize h1 x
        linarith
      rw [h2] at h5
      linarith
    exact h4
  · -- Now the reverse direction: if f(x) = 1/2 - x, then it satisfies the functional equation
    intro hf
    rw [hf]
    intro x y
    simp
    <;> ring_nf <;> linarith