import Mathlib
/- Let $\alpha$ be a non-zero real number. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
x f(x+y)=(x+\alpha y) f(x)+x f(y)
$$

for all $x, y \in \mathbb{R}$.
Answer: $f(x)=c x^{2}$ for any real constant $c$ if $\alpha=2 ; f(x)=0$ otherwise. -/
theorem algebra_605045 (a : ℝ) (hane0 : a ≠ 0) (f : ℝ → ℝ) : (a = 2 → ((∀ x y : ℝ, x * f (x + y) = (x + a * y) * f x + x * f y) ↔ (∃ c : ℝ, ∀ x : ℝ, f x = c * x ^ 2))) ∧ (a ≠ 2 → ((∀ x y : ℝ, x * f (x + y) = (x + a * y) * f x + x * f y) ↔ (∀ x : ℝ, f x = 0))):= by

    -- Split into two cases: a = 2 and a ≠ 2
    constructor
    .
      -- Case 1: When a = 2
      intro ha
      subst a
      constructor
      .
        intro h
        -- First prove f(0) = 0
        have h1 : f 0 = 0:= by
          specialize h 1 0
          simp at h
          exact h
        -- Prove f is even: f(x) = f(-x)
        have h2 : ∀ x : ℝ, f x = f (-x):= by
          intro x
          have g1:= h x (-x)
          simp at g1
          rw [h1] at g1
          ring_nf at g1
          replace g1 : x * (f x - f (-x)) = 0:= by linarith
          simp at g1
          rcases g1 with g1 | g1
          .
            subst x
            simp
          .
            linarith

        -- Key functional equation 1
        have h3 : ∀ x y : ℝ, (x - y) * f (x + y) = (x + y) * (f x - f y):= by
          intro x y
          have g1:= h x y
          have g2:= h y x
          ring_nf at g1 g2
          ring_nf
          linarith

        -- Key functional equation 2
        have h4 : ∀ x y : ℝ, (x + y) * f (x - y) = (x - y) * (f x - f y):= by
          intro x y
          specialize h3 x (-y)
          rw [←(h2 y)] at h3
          ring_nf at h3
          ring_nf
          linarith

        -- Prove f(z) = f(1)z² for all z
        have h5 : ∀ z : ℝ, f z = f 1 * z ^ 2:= by
          intro z
          have g1:= h3 ((z + 1) / 2) ((z - 1) / 2)
          have g2:= h4 ((z + 1) / 2) ((z - 1) / 2)
          ring_nf at g1 g2
          rw [show z * f (1 / 2 + z * (1 / 2)) - z * f (-1 / 2 + z * (1 / 2)) = z * (f (1 / 2 + z * (1 / 2)) - f (-1 / 2 + z * (1 / 2))) by ring] at g1
          rw [←g2] at g1
          linarith
        use (f 1)
      .
        -- Verify that f(x) = cx² is indeed a solution when a = 2
        intro h
        rcases h with ⟨c, h⟩
        simp [h]
        intro x y
        linarith
    .
      -- Case 2: When a ≠ 2
      intro ha
      constructor
      .
        intro h
        -- First prove f(0) = 0
        have h1 : f 0 = 0:= by
          specialize h 1 0
          simp at h
          exact h

        -- Prove f is even: f(x) = f(-x)
        have h2 : ∀ x : ℝ, f x = f (-x):= by
          intro x
          have g1:= h x (-x)
          have g2:= h (-x) x
          simp at g1 g2
          rw [h1] at g1 g2
          ring_nf at g1 g2
          have g3 : a * x * (f x - f (-x)) = 0:= by linarith
          simp [hane0] at g3
          rcases g3 with g3 | g3
          .
            subst x
            simp
          .
            linarith

        -- Prove f is identically zero when a ≠ 2
        intro x
        specialize h x (-x)
        rw [←(h2 x)] at h
        ring_nf at h
        rw [h1] at h
        simp at h
        replace h : x * (2 - a) * f x = 0:= by linarith
        replace ha : 2 - a ≠ 0:= by
          by_contra H
          replace H : a = 2:= by linarith
          trivial
        simp [ha] at h
        rcases h with h | h
        .
          subst x
          rw [h1]
        .
          exact h
      .
        -- Verify that f(x) = 0 is indeed a solution when a ≠ 2
        intro h
        simp [h]
