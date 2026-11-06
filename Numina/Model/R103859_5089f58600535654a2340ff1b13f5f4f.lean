import Mathlib

theorem algebra_138249 (f : ℤ → ℤ) :
    (∀ x, f x = x * f 1) ↔ ∃ c, ∀ x, f x = c * x := by
  constructor
  · -- Assume $\forall x, f(x) = x \cdot f(1)$, we need to prove $\exists c, \forall x, f(x) = c \cdot x$
    intro h
    refine ⟨f 1, fun x => by
      rw [h x]
      ring⟩
  · -- Assume $\exists c, \forall x, f(x) = c \cdot x$, we need to prove $\forall x, f(x) = x \cdot f(1)$
    rintro ⟨c, hc⟩
    intro x
    rw [hc x]
    -- Show c = f(1)
    have h1 : f 1 = c := by
      specialize hc 1
      simp at hc
      linarith
    rw [h1]
    ring