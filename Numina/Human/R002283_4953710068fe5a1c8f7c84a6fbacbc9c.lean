import Mathlib

/- let f x = x + 1 / (x - 1), then for x ^ 2 ≠ 1, f (-x) is -/

theorem algebra_81458 {f: ℝ → ℝ} (hf: ∀ x, x ≠ 1 → f x = (x + 1) / (x - 1)):
  ∀ x, x ^ 2 ≠ 1 → f (-x) = 1 / f x := by

  intro x hx
  have f1:= hf x
  have f2:= hf (-x)
  have u: ¬ x = 1 := by
    by_contra! o
    simp [o] at hx
  have v: ¬ -x = 1 := by
    by_contra! o
    replace o: x = -1 := by linarith
    simp [o] at hx
  simp [u, v] at f1 f2
  simp [f1, f2]

  -- then we show the denominator is not 0
  have o1: -x - 1 ≠ 0 := by
    by_contra! o
    replace o: x = -1 := by linarith
    simp [o] at hx
  have o2: x - 1 ≠ 0 := by
    by_contra! o
    replace o: x = 1 := by linarith
    simp [o] at hx
  have o3: x + 1 ≠ 0 := by
    by_contra! o
    replace o: x = -1 := by linarith
    simp [o] at hx

  -- finally, use field_simo to simplify
  field_simp
  ring

