import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_174850 {f : ℕ → ℝ → ℝ}
  (hf0 : ∀ x, f 0 x = 3 * sin x)
  (hfn : ∀ n x, f (n + 1) x = 9 / (3 - f n x)) :
  f 2023 (π / 6) = 6 := by

  have h1 : f 0 (π / 6) = 3 / 2 := by
    rw [hf0]
    have h2 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    rw [h2]
    norm_num

  have h2 : f 1 (π / 6) = 6 := by
    rw [hfn 0 (π / 6), h1]
    norm_num

  have h3 : f 2 (π / 6) = -3 := by
    rw [hfn 1 (π / 6), h2]
    norm_num

  have h4 : f 3 (π / 6) = 3 / 2 := by
    rw [hfn 2 (π / 6), h3]
    norm_num

  have h5 : ∀ k, f (3 * k + 1) (π / 6) = 6 := by
    intro k
    induction k with
    | zero =>
      norm_num at *
      exact h2
    | succ k ih =>
      have eq1 : f (3 * (k + 1) + 1) (π / 6) = f (3 * k + 4) (π / 6) := by
        ring_nf
      rw [eq1]
      have h6 : f (3 * k + 4) (π / 6) = 9 / (3 - f (3 * k + 3) (π / 6)) := by
        apply hfn
      have h7 : f (3 * k + 3) (π / 6) = 9 / (3 - f (3 * k + 2) (π / 6)) := by
        apply hfn
      have h8 : f (3 * k + 2) (π / 6) = 9 / (3 - f (3 * k + 1) (π / 6)) := by
        apply hfn
      rw [h6, h7, h8, ih]
      norm_num
      all_goals try { linarith }

  have h2023 : 2023 = 3 * 674 + 1 := by norm_num
  rw [h2023]
  apply h5
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }