import Mathlib

open Real

theorem algebra_325430 (f : ℝ → ℝ) (hf : f = fun x => (6 * x ^ 2 + 4 * x + 3) / (3 * x ^ 2 + 2 * x + 1)) :
    IsGreatest (Set.image f {x | ∃ y, f x = y ∧ y ≤ 7 / 2}) (7 / 2) := by
  constructor
  · -- Show that 7/2 is in the image of f.
    use -1 / 3
    constructor
    · -- Show that -1/3 is in the domain
      norm_num [hf]
    · -- Show that f(-1/3) = 7/2
      norm_num [hf]

  · -- Show 7/2 is the greatest
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : (6 * x ^ 2 + 4 * x + 3) / (3 * x ^ 2 + 2 * x + 1) ≤ 7 / 2 := by
      have h2 : 3 * x ^ 2 + 2 * x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 3)]
      apply (div_le_iff₀ h2).mpr
      nlinarith [sq_nonneg (x + 1 / 3)]
    simp [hf] at h1 ⊢
    linarith