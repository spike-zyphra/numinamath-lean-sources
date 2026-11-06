import Mathlib
/- Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$such that

$$
f(x+f(y+x y))=(y+1) f(x+1)-1
$$

for all $x, y \in \mathbb{R}^{+}$.
( $\mathbb{R}^{+}$denotes the set of positive real numbers.) -/
theorem algebra_609857 (f : ℝ → ℝ) (hpos : ∀ x : ℝ, x > 0 → f x > 0) : (∀ x y : ℝ, x > 0 → y > 0 → f (x + f (y + x * y)) = (y + 1) * f (x + 1) - 1) ↔ (∀ x : ℝ, x > 0 → f x = x):= by
  constructor
  .
    intro h
    -- Proves that f is injective: if f(x) = f(y) then x = y for positive x, y
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → f x = f y → x = y:= by
      intro x y hx hy hxy
      have g1:= h 1 (x / 2) (by linarith) (by linarith)
      have g2:= h 1 (y / 2) (by linarith) (by linarith)
      simp at g1 g2
      rw [hxy] at g1
      rw [show (1 : ℝ) + 1 = 2 by ring_nf] at g1 g2
      have g3 : f 2 * (x - y) = 0:= by linarith
      specialize hpos 2 (by linarith)
      replace hpos : f 2 ≠ 0:= by linarith
      simp [hpos] at g3
      linarith

    -- Proves that f((x+1)/f(x+1)) = 1 for positive x
    have h2 : ∀ x : ℝ, x > 0 → f ((x + 1) / f (x + 1)) = 1:= by
      intro x hx
      specialize h x (1 / f (x + 1)) (by linarith) (by specialize hpos (x + 1) (by linarith) ; positivity)
      have g1:= hpos (x + 1) (by linarith)
      rw [show 1 / f (x + 1) + x * (1 / f (x + 1)) = (x + 1) / f (x + 1) by ring_nf] at h
      rw [show (1 / f (x + 1) + 1) * f (x + 1) - 1 = f (x + 1) by field_simp] at h
      have g2:= hpos ((x + 1) / f (x + 1)) (by positivity)
      replace h:= h1 (x + f ((x + 1) / f (x + 1))) (x + 1) (by linarith) (by linarith) h
      linarith

    -- Proves that there exists a positive constant c such that f(x) = cx for x > 1
    have h3 : ∃ c : ℝ, c > 0 ∧ (∀ x : ℝ, x > 1 → f x = c * x):= by
      use (f 2 / 2)
      refine ⟨(by specialize hpos 2 (by linarith) ; positivity), ?_⟩
      intro x hx
      have g1:= h2 1 (by linarith)
      ring_nf at g1
      field_simp at g1
      have g2:= h2 (x - 1) (by linarith)
      ring_nf at g2
      field_simp at g2
      specialize h1 (2 / f 2) (x / f x) (by specialize hpos 2 (by linarith) ; positivity) (by specialize hpos x (by linarith) ; positivity) (by linarith)
      have g3:= hpos x (by linarith)
      have g4:= hpos 2 (by linarith)
      field_simp at h1
      field_simp
      linarith

    -- Proves that the constant c must equal 1
    rcases h3 with ⟨c, hc, h3⟩
    have h4 : c = 1:= by
      have g1:= h 1 1 (by linarith) (by linarith)
      ring_nf at g1
      rw [h3 2 (by linarith)] at g1
      rw [h3 (1 + c * 2) (by linarith)] at g1
      replace g1 : (2 * c - 1) * (c - 1) = 0:= by linarith
      simp at g1
      rcases g1 with g1 | g1
      .
        replace g1 : c = 1 / 2:= by linarith
        by_contra _
        subst c
        specialize h 1 2 (by linarith) (by linarith)
        ring_nf at h
        rw [h3 4 (by linarith)] at h
        ring_nf at h
        rw [h3 3 (by linarith)] at h
        rw [h3 2 (by linarith)] at h
        ring_nf at h
        linarith
      .
        linarith

    -- Completes the forward direction by showing f(x) = x for all positive x
    subst c
    simp at h3
    intro y hy
    specialize h 1 (y / 2) (by linarith) (by linarith)
    ring_nf at h
    rw [h3 2 (by linarith)] at h
    ring_nf at h
    rw [←h3 (1 + y) (by linarith)] at h
    replace h:= h1 (1 + f y) (1 + y) (by specialize hpos y hy ; linarith) (by linarith) h
    linarith
  .
    -- Proves the reverse direction: if f(x) = x, then the functional equation holds
    intro h
    intro x y hx hy
    rw [h (y + x * y) (by positivity)]
    rw [h (x + 1) (by linarith)]
    rw [h (x + (y + x * y)) (by positivity)]
    linarith
