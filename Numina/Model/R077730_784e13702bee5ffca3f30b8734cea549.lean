import Mathlib

theorem algebra_115713 (f : ℕ → ℕ) :
    (∀ x y, f (x + y) = f x + f y) ↔ ∃ c, ∀ x, f x = c * x := by
  constructor
  · -- Assume f satisfies the functional equation, prove there exists c such that ∀ x, f x = c * x
    intro h
    use f 1
    intro x
    induction x with
    | zero =>
      have h0 : f 0 = 0 := by
        have eq := h 0 0
        simp at eq
        omega
      simp [h0]
    | succ x ih =>
      have eq1 := h x 1
      simp at eq1 ⊢
      rw [ih] at eq1
      linarith [eq1]
  · -- Assume there exists c such that ∀ x, f x = c * x, prove f satisfies the functional equation
    rintro ⟨c, hc⟩
    intro x y
    have h1 : f (x + y) = c * (x + y) := by
      apply hc
    have h2 : f x = c * x := by
      apply hc
    have h3 : f y = c * y := by
      apply hc
    calc
      f (x + y) = c * (x + y) := by rw [h1]
      _ = c * x + c * y := by ring
      _ = f x + f y := by rw [h2, h3]