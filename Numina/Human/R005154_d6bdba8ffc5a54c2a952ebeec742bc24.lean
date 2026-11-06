import Mathlib
/- Trouver les fonctions $f: \mathbb{R} \mapsto \mathbb{R}$ telles que, pour tous les réels $x$ et $y$, on ait:

$$
f\left(x^{2}+x+f(y)\right)=y+f(x)+f(x)^{2}
$$ -/

theorem algebra_605864 (f : ℝ → ℝ) : (∀ x y : ℝ, f (x ^ 2 + x + f y) = y + f x + f x ^ 2) ↔ (∀ x : ℝ, f x = x):= by
    constructor
    -- Forward direction: proving that the functional equation implies f(x) = x
    .
      intro h
      -- Prove that f is injective (one-to-one)
      have h1 : ∀ x y : ℝ, f x = f y → x = y:= by
        intro x y hxy
        have g1:= h 0 x
        have g2:= h 0 y
        simp at g1 g2
        rw [hxy] at g1
        linarith
      -- Prove a key property: f(-1-x) = -1-f(x) and f(x) ≠ -1/2 when x ≠ -1/2
      have h2 : ∀ x : ℝ, x ≠ -1 / 2 → f (-1 - x) = -1 - f x ∧ f x ≠ -1 / 2:= by
        intro x hx
        have g1:= h x 0
        have g2:= h (-1 - x) 0
        ring_nf at g1 g2
        have g3 : (f (-1 - x) - f x) * (f (-1 - x) + 1 + f x) = 0:= by linarith
        have g4 : f (-1 - x) - f x ≠ 0:= by
          by_contra H
          replace H : f (-1 - x) = f x:= by linarith
          specialize h1 (-1 - x) x H
          replace h1 : x = -1 / 2:= by linarith
          trivial
        simp [g4] at g3
        constructor
        .
          linarith
        .
          by_contra H
          rw [H] at g3
          replace g3 : f (-1 - x) = -1 / 2:= by linarith
          rw [←H] at g3
          specialize h1 (-1 - x) x g3
          replace h1 : x = -1 / 2:= by linarith
          trivial
      -- Prove that f is surjective (onto)
      have h3 : ∀ a : ℝ, ∃ b : ℝ, f b = a:= by
        intro a
        use (f (a - f 0 - f 0 ^ 2))
        specialize h 0 (a - f 0 - f 0 ^ 2)
        simp at h
        linarith
      -- Prove that f(-1/2) = -1/2
      have h4 : f (-1 / 2) = -1 / 2:= by
        specialize h3 (-1 / 2)
        rcases h3 with ⟨b, hb⟩
        have g1 : b = -1 / 2:= by
          by_contra H
          specialize h2 b H
          replace h2:= h2.2
          trivial
        rw [g1] at hb
        exact hb
      -- Prove a stepping property: if f(y) = y, then f(y±1/4) = y±1/4
      have h5 : ∀ y : ℝ, f y = y → f (y - 1 / 4) = y - 1 / 4 ∧ f (y + 1 / 4) = y + 1 / 4:= by
        intro y hy
        have g1:= h (-1 / 2) y
        rw [h4, hy] at g1
        ring_nf at g1
        ring_nf
        simp [g1]
        ring_nf
        specialize h3 (1 / 4 + y)
        rcases h3 with ⟨b, hb⟩
        have g2:= h (-1 / 2) b
        rw [hb, h4] at g2
        ring_nf at g2
        rw [hy] at g2
        replace g2 : b = 1 / 4 + y:= by linarith
        rw [g2] at hb
        exact hb
      -- Prove that f(0) = 0 and f(1/4) = 1/4
      have h6 : f 0 = 0 ∧ f (1 / 4) = 1 / 4:= by
        have g1:= h5 (-1 / 2) h4
        ring_nf at g1
        replace g1:= g1.2
        have g2:= h5 (-1 / 4) g1
        ring_nf at g2
        replace g2:= g2.2
        have g3:= h5 0 g2
        ring_nf at g3
        replace g3:= g3.2
        rw [g2, g3]
        simp
      rcases h6 with ⟨h6, h7⟩
      -- Prove that f is an involution: f(f(y)) = y
      have h9 : ∀ y : ℝ, f (f y) = y:= by
        intro y
        specialize h 0 y
        simp at h
        rw [h6] at h
        simp at h
        exact h
      -- Prove that f preserves non-negativity
      have h10 : ∀ t : ℝ, t ≥ 0 → f t ≥ 0:= by
        intro t ht
        have g1 : ∃ x : ℝ, x ^ 2 + x + 1 / 4 = t:= by
          use (-1 / 2 + √t)
          ring_nf
          exact Real.sq_sqrt ht
        rcases g1 with ⟨x, hx⟩
        specialize h x (1 / 4)
        rw [h7, hx] at h
        rw [h]
        have g1 : (f x + 1 / 2) ^ 2 ≥ 0:= by positivity
        linarith
      -- Prove additivity for non-negative first argument
      have h11 : ∀ t : ℝ, t ≥ 0 → ∀ y : ℝ, f (t + y) = f t + f y:= by
        intro t ht y
        have g1 : ∃ z : ℝ, z ^ 2 + z = t:= by
          use (-1 / 2 + √(t + 1 / 4))
          ring_nf
          suffices √(1 / 4 + t) ^ 2 = 1 / 4 + t by linarith
          exact Real.sq_sqrt (by linarith)
        rcases g1 with ⟨z, hz⟩
        have g2:= h z 0
        rw [h6] at g2
        simp at g2
        specialize h z (f y)
        rw [hz, h9 y] at h
        rw [hz] at g2
        linarith
      -- Prove that f is monotone
      have h12 : ∀ x y : ℝ, x ≥ y → f x ≥ f y:= by
        intro x y hxy
        specialize h11 (x - y) (by linarith) y
        ring_nf at h11
        specialize h10 (x - y) (by linarith)
        linarith
      intro x
      by_contra H
      replace H : f x < x ∨ f x > x:= by exact lt_or_gt_of_ne H
      rcases H with H | H
      .
        have g1:= h12 x (f x) (by linarith)
        rw [h9 x] at g1
        have g2:= h12 (f x) x (by linarith)
        rw [h9 x] at g2
        linarith
      .
        have g1:= h12 (f x) x (by linarith)
        rw [h9 x] at g1
        have g2:= h12 x (f x) (by linarith)
        rw [h9 x] at g2
        linarith
    -- Backward direction: proving that if f(x) = x, then it satisfies the functional equation
    .
      intro h
      simp [h]
      intro x y
      linarith
