import Mathlib

open Finset

theorem algebra_3282 {f : ℕ → ℝ}
    (hf : ∀ r, f r = ∑ i ∈ Icc 1 r, (1 : ℝ) / i) (n : ℕ) (hn : 0 < n) :
    ∑ r ∈ Icc 1 n, f r = (n + 1) * f n - n := by
  have h1 : ∀ (n : ℕ), ∑ r in Icc 1 n, f r = (↑n + 1) * f n - ↑n := by
    intro n
    induction n with
    | zero =>
      simp [hf]
    | succ n ih =>
      rw [sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h2 : f (n + 1) = f n + (1 : ℝ) / ((↑n + 1 : ℝ)) := by
        rw [hf (n + 1), hf n]
        simp [sum_Icc_succ_top, add_assoc]
        <;> ring
      rw [h2]
      field_simp at *
      ring
  specialize h1 n
  simpa using h1