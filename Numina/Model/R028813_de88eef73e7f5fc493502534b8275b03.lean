import Mathlib

theorem algebra_94158 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + p * x + q) :
    IsLeast (Set.range f) (f (-p / 2)) := by
  have h1 : ∀ x, f x = x ^ 2 + p * x + q := by
    intro x
    rw [hf]

  have h2 : f (-p / 2) = q - p ^ 2 / 4 := by
    rw [h1]
    ring_nf

  have h3 : ∀ x, f x ≥ f (-p / 2) := by
    intro x
    rw [h1 x, h2]
    have h4 : (x + p / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [sq_nonneg (x + p / 2)]

  constructor
  · -- Show that f(-p/2) is indeed in the range
    use -p / 2
    all_goals simp [h2]
    <;> linarith

  · -- Show that f(-p/2) is the least value in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h4 : f x ≥ f (-p / 2) := h3 x
    linarith [h4, hx]