import Mathlib

theorem algebra_606093 {f : ℝ → ℝ} : (∀ x y, f (y * f (x + y) + f x) = 4 * x + 2 * y * f (x + y)) ↔ ∀ x, f x = 2 * x := by
  constructor
  · -- Forward direction: proving that the functional equation implies f(x) = 2x
    intro h
    -- First key property: f(f(x)) = 4x for all x
    have h1 : ∀ x : ℝ, f (f x) = 4 * x:= by
        intro x
        specialize h x 0
        simp at h
        exact h
    -- Prove f(0) = 0 using the property f(f(x)) = 4x
    have h2 : f 0 = 0:= by
        have g1:= h1 0
        specialize h1 (f 0)
        simp at g1
        rw [g1] at h1
        linarith
    -- Prove f(1) = 2 using the original equation and f(0) = 0
    have h3 : f 1 = 2:= by
        specialize h 0 1
        simp at h
        rw [h2] at h
        simp at h
        specialize h1 1
        rw [h] at h1
        linarith
    -- Prove f(2) = 4 using f(1) = 2 and f(f(x)) = 4x
    have h4 : f 2 = 4:= by
        replace h3 : f (f 1) = f 2:= by rw [h3]
        specialize h1 1
        linarith
    intro x
    -- Final step: prove f(x) = 2x for all x
    have h5 : f (2 * (1 - x) + f x) = f 2:= by
        specialize h x (1 - x)
        rw [h4]
        simp at h
        rw [h3] at h
        ring_nf at h
        ring_nf
        exact h
    have h5' : f (2 * (1 - x) + f x) = 4 := by
      linarith [h5, h4]
    -- From h5' we know that f(2*(1-x) + f(x)) = 4, which implies 2*(1-x) + f(x) = 2
    have h6 : ∀ z : ℝ, f z = 4 → z = 2 := by
      intro z hz
      have h1z : f (f z) = 4 * z := h1 z
      rw [hz] at h1z
      have h12 : f 4 = 8 := by
        have h11 : f (f 2) = 8 := by
          specialize h1 2
          norm_num at h1
          linarith
        rw [h4] at h11
        linarith
      nlinarith [h1z, h4, h12, hz]
    specialize h6 (2 * (1 - x) + f x) h5'
    -- From the equation 2*(1-x) + f(x) = 2, we can solve for f(x) and get f(x) = 2x
    linarith [h6]
  · -- Backward direction: proving that f(x) = 2x implies the functional equation
    intro hf x y
    have hfx : f x = 2 * x := hf x
    have hfxy : f (x + y) = 2 * (x + y) := hf (x + y)
    simp [hfx, hfxy, hf]
    <;> ring_nf
    <;> linarith