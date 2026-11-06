import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_116757 {f : ℝ → ℝ → ℝ} (hf : f = λ x y => x^2 - y^2)
  (g : ℝ → ℝ → ℝ) (hg : g = λ x y => x^2 + 4 * y^2 - 4 * x) :
  IsGreatest {z | ∃ x y, z = f x y ∧ g x y = 0} (f 4 0) ∧
  IsLeast {z | ∃ x y, z = f x y ∧ g x y = 0} (f (2 / 5) (3 / 5)) := by 
  constructor 
  · -- Show that f 4 0 is the greatest 
    constructor 
    · -- Show that f 4 0 is in the set
      use 4, (0 : ℝ)
      norm_num [hf, hg]
    · -- Show that all z in the set ≤ f 4 0
      intro z hz 
      rcases hz with ⟨x, y, hfx, hgx⟩ 
      simp [hf, hg] at hfx hgx
      have h2 : x^2 + 4 * y^2 - 4 * x = 0 := by nlinarith 
      have h3 : z ≤ 16 := by 
        have h4 : (x - 4) ^ 2 ≥ 0 := by 
          nlinarith 
        nlinarith [sq_nonneg (y), sq_nonneg (x - 4), sq_nonneg (y - 0), sq_nonneg (x - 2), sq_nonneg (x - 2 / 5), sq_nonneg (y - 3 / 5), sq_nonneg (x - 4)]
      have h4 : f 4 0 = 16 := by 
        rw [hf]
        norm_num 
      linarith [hfx, h3, h4]
  · -- Show that f (2 / 5) (3 / 5) is the least
    constructor 
    · -- Show that f (2 / 5) (3 / 5) is in the set 
      use (2 / 5 : ℝ), (3 / 5 : ℝ)
      norm_num [hf, hg]
    · -- Show that all z in the set ≥ f (2 / 5) (3 / 5)
      intro z hz 
      rcases hz with ⟨x, y, hfx, hgx⟩ 
      simp [hf, hg] at hfx hgx 
      have h2 : x^2 + 4 * y^2 - 4 * x = 0 := by nlinarith
      have h5 : z ≥ -1 / 5 := by 
        nlinarith [sq_nonneg (y - 3 / 5), sq_nonneg (x - 2 / 5), sq_nonneg (x ^ 2 * 4 - (x * 4) ^ 2), sq_nonneg (x - 4), sq_nonneg (x - 2), sq_nonneg (y ^ 2 - (3 / 5) ^ 2)]
      have h6 : f (2 / 5) (3 / 5) = -1 / 5 := by 
        rw [hf]
        norm_num
      linarith [hfx, h5, h6]