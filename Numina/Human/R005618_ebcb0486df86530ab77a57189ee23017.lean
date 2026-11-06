import Mathlib
/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that, for all real numbers $x, y$,

$$
(x-y)(f(x)-f(y))=f(x-f(y)) f(f(x)-y)
$$ -/
theorem algebra_609144 (f : ℝ → ℝ) : (∀ x y : ℝ, (x - y) * (f x - f y) = f (x - f y) * f (f x - y)) ↔ ((∀ x : ℝ, f x = 0) ∨ (∀ x : ℝ, f x = x)):= by
  constructor
  .
    intro h
    -- First prove that f(0) = 0
    have h1 : f 0 = 0:= by
      by_contra H
      have g1:= h 0 0
      simp at g1
      rcases g1 with g1 | g1
      .
        have g2:= h 0 (-f 0)
        simp at g2
        rw [g1] at g2
        simp at g2
        simp [H] at g2
        ring_nf at g2
        have g3:= h 0 (f 0 * 2)
        have g4:= h (f 0 * 2) 0
        rw [show (0 - f 0 * 2) * (f 0 - f (f 0 * 2)) = (f 0 * 2 - 0) * (f (f 0 * 2) - f 0) by linarith] at g3
        rw [g4] at g3
        clear g4
        ring_nf at g3
        rw [g1] at g3
        rw [←g2] at g3
        simp at g3
        have g4:= h (f 0) 0
        ring_nf at g4
        rw [g3] at g4
        simp at g4
        replace g4 : f 0 ^ 2 = 0:= by linarith
        simp at g4
        trivial
      .
        have g2:= h (f 0) 0
        ring_nf at g2
        rw [g1] at g2
        simp at g2
        replace g2 : f 0 ^ 2 = 0:= by linarith
        simp at g2
        trivial

    -- Prove that for all x, x * f(x) = f(x) * f(f(x))
    have h2 : ∀ x : ℝ, x * f x = f x * (f (f x)):= by
      intro x
      specialize h x 0
      rw [h1] at h
      ring_nf at h
      exact h

    -- Prove that for all x, either f(x) = 0 or f(x) = x
    have h3 : ∀ x : ℝ, f x = 0 ∨ f x = x:= by
      intro x
      have g1:= h x (f x)
      rw [show f x - f x = 0 by linarith] at g1
      rw [h1] at g1
      simp at g1
      replace g1 : f x = f (f x):= by
        rcases g1 with g1 | g1
        .
          replace g1 : f x = x:= by linarith
          rw [g1]
          linarith
        .
          linarith
      specialize h2 x
      rw [←g1] at h2
      replace h2 : f x * (f x - x) = 0:= by linarith
      simp at h2
      rcases h2 with h2 | h2
      .
        left
        exact h2
      .
        right
        linarith

    -- Case analysis: either f is constantly zero or f is the identity function
    by_cases h4 : ∀ x : ℝ, f x = 0
    .
      simp [h4]
    .
      simp at h4
      rcases h4 with ⟨a, ha⟩
      have hane0 : a ≠ 0:= by
        by_contra H
        subst a
        trivial
      replace ha : f a = a:= by
        specialize h3 a
        simp [ha] at h3
        exact h3

      -- Prove that for any y where a-y ≠ 0, f(a-y) = a-y
      have h4 : ∀ y : ℝ, a - y ≠ 0 → f (a - y) = a - y:= by
        intro y hay
        by_cases hy : f y ≠ 0
        .
          replace hy : f y = y:= by
            specialize h3 y
            simp [hy] at h3
            exact h3
          specialize h a y
          rw [ha, hy] at h
          replace h : (f (a - y) - (a - y)) * (f (a - y) + (a - y)) = 0:= by linarith
          simp at h
          rcases h with h | h
          .
            linarith
          .
            have h4 : f (a - y) ≠ 0:= by
              by_contra H
              rw [H] at h
              simp at h
              trivial
            replace h4 : f (a - y) = a - y:= by
              specialize h3 (a - y)
              simp [h4] at h3
              exact h3
            rw [h4] at h
            simp at h
            trivial
        .
          simp at hy
          specialize h a y
          rw [ha, hy] at h
          simp at h
          rw [ha] at h
          replace h : a * (f (a - y) - (a - y)) = 0:= by linarith
          simp [hane0] at h
          linarith

      -- Complete the proof that f is the identity function
      right
      intro x
      by_cases hx : x = 0
      .
        subst x
        rw [h1]
      .
        specialize h4 (a - x) (by ring_nf; exact hx)
        ring_nf at h4
        exact h4
  .
    intro h
    rcases h with h | h
    all_goals
      simp [h]
