import Mathlib

open Real

/-if f(1 + cosx) = sin x ^ 2 + cos x - 1, then f x = ? -/

theorem algebra_308326 {f: ℝ → ℝ} (hf: ∀ x, f (1 + cos x) = sin x ^ 2 + cos x - 1):
    ∀ x, x ∈ Set.Icc 0 1 → f x = - x ^ 2 + 3 * x - 2 := by

    intro x hx
    simp at hx

    -- we write x in the form of 1 + cos y
    set y:= arccos (x - 1)
    have hy: cos y = x - 1 := by
        simp [y]
        apply Real.cos_arccos
        simp [hx]
        linarith
    replace hy: x = 1 + cos y := by
        linarith [hy]

    -- then we can use hf to get the value
    rw [hy]
    specialize hf y
    rw [hf]
    clear hf hy hx
    clear_value y
    rw [Real.sin_sq]
    ring