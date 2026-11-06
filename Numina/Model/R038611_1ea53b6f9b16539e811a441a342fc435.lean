import Mathlib
theorem algebra_607711 (f : ℝ → ℝ) : (∀ x y, f (x + y) ^ 2 - f (2 * x ^ 2) = f (y + x) * f (y - x) + 2 * x * f y) ↔
(∀ x, f x = 0) ∨ (∀ x, f x = x) := by
  constructor
  · -- Forward direction: proving that f must be either identically 0 or the identity function
    intro h
    -- First, prove that f(0) = 0 by setting x = y = 0 in the original equation
    have h1 : f 0 = 0:= by
        specialize h 0 0
        simp at h
        linarith
    -- Prove that f(x)² = f(-x)² for all x
    have h2 : ∀ x : ℝ, (f x) ^ 2 = (f (-x)) ^ 2:= by
        intro x
        have g1:= h x 0
        have g2:= h (-x) 0
        simp at g1 g2
        rw [h1] at g1 g2
        simp at g1 g2
        linarith
    -- Prove that x·f(y) = y·f(x) for all x,y
    have h3 : ∀ x y : ℝ, x * f y = y * f x:= by
        intro x y
        have g1:= h (-x) y
        have g2:= h x y
        ring_nf at g1 g2
        have g3 : (f (x + y)) ^ 2 - (f (-x + y)) ^ 2 =  4 * x * f y:= by linarith
        clear g1 g2
        have g1:= h (-y) x
        have g2:= h y x
        ring_nf at g1 g2
        have g4 : (f (y + x)) ^ 2 - (f (-y + x)) ^ 2 = 4 * y * f x:= by linarith
        clear g1 g2
        specialize h2 (-x + y)
        rw [show -(-x + y) = -y + x by ring] at h2
        rw [show x + y = y + x by ring] at g3
        linarith
    -- Show that f(x) = x * f(1)
    have h4 : ∀ x : ℝ, f x = x * f 1 := by
        intro x
        have h5 := h3 x 1
        simp at h5
        linarith
    have h5 : f 1 = 0 ∨ f 1 = 1 := by
        -- Let $x = y = 1/2$. Then the equation becomes:
        -- $f(1)^2 - f(1/2) = f(1)f(0) + f(1/2)$.
        have eq1 := h (1 / 2) (1 / 2)
        have eq2 : f (1 / 2 + 1 / 2) = f 1 := by ring_nf
        have eq4 : f (2 * (1 / 2) ^ 2) = f (1 / 2) := by
            ring_nf
        have eq5 : f (1 / 2 - 1 / 2) = f 0 := by
            ring_nf
        rw [eq2, eq4, eq5] at eq1
        have eq6 : f (1 / 2) = (1 / 2) * f 1 := by
            specialize h4 (1 / 2)
            norm_num at h4 ⊢
            linarith
        rw [eq6] at eq1
        have eq7 : f 1 ^ 2 - f 1 = 0 := by
            nlinarith [h1, eq1]
        have eq8 : f 1 * (f 1 - 1) = 0 := by
            nlinarith
        cases (mul_eq_zero.mp eq8) with
        | inl h =>
            left
            linarith
        | inr h =>
            right
            linarith
    cases h5 with
    | inl h5 =>
        left
        intro x
        specialize h4 x
        rw [h5] at h4
        nlinarith
    | inr h5 =>
        right
        intro x
        specialize h4 x
        rw [h5] at h4
        nlinarith
  · -- Reverse direction: proving that both given functions satisfy the equation
    rintro (h | h)
    · -- Case where f(x) = 0 for all x
      intro x y
      simp [h]
    · -- Case where f(x) = x for all x
      intro x y
      simp [h]
      ring