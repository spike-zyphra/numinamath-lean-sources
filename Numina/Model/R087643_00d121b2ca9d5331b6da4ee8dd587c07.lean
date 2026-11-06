import Mathlib

theorem algebra_109718 {f : ℝ → ℝ} (hf : f = fun x => x + x ^ 2) :
    IsLeast (Set.range f) (f (-0.5)) := by
  constructor
  · -- Show that f(-0.5) is in the range of f
    simpa using by norm_num [hf]
  · -- Show that f(-0.5) is the smallest element in the range of f
    intro y hy
    rcases hy with ⟨z, hz⟩
    have h1 : f z = y := hz
    have h2 : f z = z + z ^ 2 := by
      rw [hf]
    have h3 : f (-0.5) = -0.25 := by
      rw [hf]
      norm_num
    have h4 : z + z ^ 2 ≥ -0.25 := by
      nlinarith [sq_nonneg (z + 0.5)]
    have h5 : f (-0.5) ≤ y := by
      have : y = z + z ^ 2 := by
        linarith [h1, h2]
      linarith [h3, this, h4]
    linarith [h5]