import Mathlib
/-Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$such that
$$
f(x+f(x)+f(y))=2 f(x)+y
$$
holds for all $x, y \in \mathbb{R}^{+}$.-/
theorem algebra_606037 (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0) : (∀ x y : ℝ, x > 0 → y > 0 → f (x + f x + f y) = 2 * f x + y) ↔ (∀ x > 0, f x = x) := by
  -- Define helper predicates for cleaner notation
  set P : ℝ × ℝ → Prop:= fun (x, y) => f (x + f x + f y) = 2 * f x + y with hP
  set Q : ℝ → Prop:= fun x => f x = x with hQ
  clear_value P Q
  constructor
  . -- Forward direction (=>)
    intro h
    -- Rewrite the main hypothesis using predicate P
    replace h : ∀ x y : ℝ, x > 0 → y > 0 → P (x, y) := by
      intro x y hx hy
      simp [hP]
      specialize h x y hx hy
      exact h
    -- Prove that f is injective on positive reals
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → f x = f y → x = y := by
      intro x y hx hy hxy
      have g1:= h 1 x (by linarith) hx
      have g2:= h 1 y (by linarith) hy
      simp [hP] at g1 g2
      rw [hxy] at g1
      linarith
    -- Show that f(x + 2f(x)) = x + 2f(x)
    have h2 : ∀ x > 0, Q (x + 2 * f x):= by
      intro x hx
      specialize h x x hx hx
      simp [hP] at h
      simp [hQ]
      ring_nf at h
      ring_nf
      exact h
    -- Show that f(2x + 5f(x)) = 2x + 5f(x)
    have h3 : ∀ x > 0, Q (2 * x + 5 * f x):= by
      intro x hx
      specialize hf x hx
      have g1:= h x (x + 2 * f x) hx (by linarith)
      simp [hP] at g1
      simp [hQ]
      have g2:= h2 x hx
      simp [hQ] at g2
      rw [g2] at g1
      ring_nf at g1
      have g3:= h x (2 * x + 3 * f x) hx (by linarith)
      simp [hP] at g3
      ring_nf at g3
      rw [g1] at g3
      ring_nf at g3
      ring_nf
      exact g3
    -- Key lemma: if f(x)=x and f(2x+y)=2x+y, then f(y)=y
    have h4 : ∀ x y : ℝ, x > 0 → y > 0 → Q x → Q (2 * x + y) → Q y:= by
      intro x y hx hy g1 g2
      specialize h x y hx hy
      simp [hP] at h
      simp [hQ] at g1 g2
      rw [g1] at h
      ring_nf at h
      ring_nf at g2
      specialize hf y hy
      rw [←g2] at h
      specialize h1 (x * 2 + f y) (x * 2 + y) (by linarith) (by linarith) h
      simp [hQ]
      linarith
    -- Prove that f(f(x)) = f(x) for all x > 0
    have h5 : ∀ x > 0, Q (f x):= by
      intro x hx
      specialize h2 x hx
      specialize h3 x hx
      rw [show 2 * x + 5 * f x = 2 * (x + 2 * f x) + f x by linarith] at h3
      specialize hf x hx
      specialize h4 (x + 2 * f x) (f x) (by linarith) (by linarith) h2 h3
      exact h4
    -- Finally prove f(x) = x for all x > 0
    intro x hx
    specialize h5 x hx
    specialize hf x hx
    simp [hQ] at h5
    specialize h1 x (f x) hx (by linarith) (by linarith)
    linarith
  . -- Backward direction (<=)
    intro h
    intro x y hx hy
    -- If f(x)=x for all x>0, then the functional equation holds
    have g1:= h x hx
    have g2:= h y hy
    have g3:= h (x + x + y) (by linarith)
    rw [g1, g2, g3]
    linarith
