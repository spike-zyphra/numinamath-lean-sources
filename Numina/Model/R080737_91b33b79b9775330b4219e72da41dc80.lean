import Mathlib

open Finset

theorem algebra_324259 {f : ℝ → ℝ} (hf : f = fun x => (1 + x) / (1 - 3 * x))
    (f_seq : ℕ → ℝ → ℝ) (h_f1 : ∀ x, f_seq 1 x = f (f x))
    (h_fn : ∀ n ≥ 2, ∀ x, f_seq n x = f (f_seq (n - 1) x)) :
    f_seq 2011 2011 = 1005 / 3017 := by
  have h1 : ∀ n, f_seq (3 * n + 1) 2011 = 1005 / 3017 := by
    intro n
    induction n with
    | zero =>
      norm_num [h_f1, hf]
      <;> field_simp
      <;> norm_num
    | succ n ih =>
      have h3 : f_seq (3 * (n + 1) + 1) 2011 = f (f_seq (3 * (n + 1) + 1 - 1) 2011) := by
        specialize h_fn (3 * (n + 1) + 1) (by omega) 2011
        simpa using h_fn
      rw [show 3 * (n + 1) + 1 - 1 = 3 * n + 3 by omega] at h3
      have h4 : f_seq (3 * n + 3) 2011 = f (f_seq (3 * n + 2) 2011) := by
        specialize h_fn (3 * n + 3) (by omega) 2011
        simpa using h_fn
      have h5 : f_seq (3 * n + 2) 2011 = f (f_seq (3 * n + 1) 2011) := by
        specialize h_fn (3 * n + 2) (by omega) 2011
        simpa using h_fn
      rw [h3, h4, h5, ih]
      norm_num [hf] at *
      <;> field_simp
      <;> ring
  have h2 : 2011 = 3 * 670 + 1 := by norm_num
  rw [h2]
  exact h1 670