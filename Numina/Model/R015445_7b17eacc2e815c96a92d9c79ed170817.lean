import Mathlib

open Finset Real

theorem algebra_11343 {f : ℝ → ℝ} (hf : f = fun x => (2 * x + 3) / (3 * x))
    (a : ℕ → ℝ) (ha1 : a 1 = 1) (han : ∀ n > 0, a (n + 1) = f (1 / a n)) :
    ∀ n > 0, a n = 2 / 3 * n + 1 / 3 := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 := ih (by linarith)
      have eq1 : a (n + 1 + 1) = f (1 / a (n + 1)) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq1]
      rw [h1]
      simp [hf]
      field_simp [show (2 / 3 * (↑n + 1 : ℝ) + 1 / 3 : ℝ) ≠ 0 by
        have h1 : (2 / 3 * (↑n + 1 : ℝ) + 1 / 3 : ℝ) > 0 := by
          nlinarith [show (↑n : ℝ) ≥ 0 by exact_mod_cast Nat.zero_le n]
        linarith
      ]
      <;> ring_nf
      <;> field_simp
      <;> ring