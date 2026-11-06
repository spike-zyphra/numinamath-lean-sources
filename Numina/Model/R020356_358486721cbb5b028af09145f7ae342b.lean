import Mathlib

theorem algebra_164771 {f : ℝ → ℝ} (hf : f = fun x => x^2 + 6 * x + 7) :
    IsLeast {y | ∃ x, y = f (f (f (f x)))} 23 := by
  constructor
  · -- First show that 23 is in the set
    use -3
    norm_num [hf]
  · -- Now show that 23 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    have h1 : ∀ x : ℝ, f x = x^2 + 6 * x + 7 := by
      intro x
      rw [hf]
    have h2 : f x ≥ -2 := by
      have hfx : f x = x^2 + 6 * x + 7 := by
        apply h1
      rw [hfx]
      nlinarith [sq_nonneg (x + 3)]
    have h3 : f (f x) ≥ -1 := by
      have hfx : f (f x) = (f x) ^ 2 + 6 * (f x) + 7 := by
        apply h1
      rw [hfx]
      nlinarith [sq_nonneg ((f x) + 2), h2]
    have h4 : f (f (f x)) ≥ 2 := by
      have hfx : f (f (f x)) = (f (f x)) ^ 2 + 6 * (f (f x)) + 7 := by
        apply h1
      rw [hfx]
      nlinarith [sq_nonneg ((f (f x)) + 1), h3]
    have h5 : f (f (f (f x)) ) ≥ 23 := by
      have hfx : f (f (f (f x)) ) = (f (f (f x)) ) ^ 2 + 6 * (f (f (f x)) ) + 7 := by
        apply h1
      rw [hfx]
      nlinarith [sq_nonneg ((f (f (f x)) ) - 2), h4]
    linarith [h5]