import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_115404 (f g : ℝ → ℝ)
  (hf : f = λ x => x^2) (hg : g = λ x => x^3) (a b : ℝ) (ha : a = 0) (hb : b = 1) :
  IsGreatest {x | ∃ t ∈ Icc a b, |f t - g t| = x} (4/27) := by
    rw [ha, hb]
    constructor
    · -- Show that 4/27 is attainable
      use 2 / 3
      constructor
      · -- Show that 2/3 ∈ [0, 1]
        norm_num
      · -- Compute |f(2/3) - g(2/3)| and show it equals 4/27
        rw [hf, hg]
        norm_num [abs_of_pos]
        all_goals norm_num
    · -- Show that 4/27 is an upper bound
      intro x hx
      rcases hx with ⟨t, ht, htfg⟩
      rw [hf, hg] at htfg
      simp at ht htfg
      have h1 : 0 ≤ t := ht.1
      have h2 : t ≤ 1 := ht.2
      have h3 : t^2 - t^3 ≥ 0 := by
        nlinarith [sq_nonneg (t - 2 / 3)]
      have h4 : |t^2 - t^3| = t^2 - t^3 := by
        rw [abs_of_nonneg h3]
      rw [h4] at htfg
      have h5 : t^2 - t^3 ≤ 4 / 27 := by
        nlinarith [sq_nonneg (t - 2 / 3)]
      linarith