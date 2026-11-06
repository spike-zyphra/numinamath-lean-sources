import Mathlib
open Real Set

theorem algebra_11242 {f g : ℝ → ℝ} (hf : ∀ x, x ≤ 1 → f x = -x^2 + x)
(hf' : ∀ x, x > 1 → f x = logb (1/3) x) (hg : ∀ x, g x = abs (x - k) + abs (x - 1))
(hfg : ∀ x1 x2, f x1 ≤ g x2) :
k ≤ 3/4 ∨ k ≥ 5/4 := by
  have h1 := hfg (1/2) 1
  have hfx1 : f (1/2) = 1/4 := by
    rw [hf (1/2) (by norm_num)]
    norm_num
  have hgx2 : g 1 = abs (1 - k) := by
    rw [hg 1]
    norm_num [abs]
    all_goals
      ring_nf
  rw [hfx1, hgx2] at h1
  cases' abs_cases (1 - k) with h2 h2
  · 
    left
    linarith
  · 
    right
    linarith