import Mathlib

/- For all real numbers $x$, the function $f$: $R$→$R$ satisfies $f (20 - x) = f (22 + x)$. It is known that $f$ has exactly two roots. What is the sum of these two roots? -/
theorem algebra_623538
  (f : ℝ → ℝ)
  (x y : ℝ)
  (hxy : x ≠ y)
  (rtx : f x = 0)
  (rty : f y = 0)
  (rtf : ∀ t, f t = 0 → t = x ∨ t = y)
  (hf : ∀ x, f (20 - x) = f (22 + x))
  : x + y = 42 :=
by
  -- If $a$ is one of the roots we can choose $x$ so that $20 - x = a$,
  -- that is, $x = 20 - a$.
  -- This gives $f(a)=f(42-a)$. So $42 - a$ is also a root.
  have : ∀ a, f a = 0 → f (42 - a) = 0 := by
    intro a h
    let x := 20 - a
    have : f (20 - x) = f (22 + x) := by
      apply hf
    simp [x] at this
    ring_nf at this
    rw [h] at this
    symm
    assumption
  rcases em (x = 21) with (h|h)
  . -- x can not be 21
    -- if so, then we can prove that we have three distinct roots
    exfalso
    subst h
    let x' := 42 - y
    have : f x' = 0 := by
      simp [x']
      apply this
      tauto
    have : x' ≠ y := by
      simp [x']
      intro c
      have : y = 21 := by linarith
      rw [this] at hxy
      simp at hxy
    have : x' ≠ 21 := by
      simp [x']
      intro c
      have : y = 21 := by linarith
      rw [this] at hxy
      simp at hxy
    have : x' = 21 ∨ x' = y := by
      apply rtf
      assumption
    rcases this with (h|h)
    . tauto
    . tauto
  . -- Rest is trivial
    have : y = 42 - x := by
      have : f (42 - x) = 0 := by
        apply this
        tauto
      have := rtf (42 - x) this
      rcases this with (h'|h')
      . have : x = 21 := by linarith
        tauto
      . linarith
    subst this
    linarith
