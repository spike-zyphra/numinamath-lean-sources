import Mathlib

theorem algebra_11655 {c d : ℝ} (f g : ℝ → ℝ) (hf : ∀ x, f x = 4 * x + c)
    (hg : ∀ x, g x = c * x + 2) (hfg : ∀ x, f (g x) = 12 * x + d) :
    d = 11 := by
  have eq1 := hfg 0
  have eq2 := hfg 1
  have eq3 : f (g 0) = d := by
    simpa using eq1
  have eq4 : f (g 0) = 8 + c := by
    have h1 : g 0 = 2 := by
      rw [hg]
      norm_num
    rw [h1]
    rw [hf]
    all_goals norm_num
    all_goals linarith
  have h_eq1 : d = 8 + c := by
    linarith [eq3, eq4]
  have eq5 : f (g 1) = 12 + d := by
    have h9 := hfg 1
    norm_num at h9 ⊢ 
    linarith
  have eq6 : f (g 1) = 5 * c + 8 := by
    have h2 : g 1 = c + 2 := by
      rw [hg]
      all_goals ring
    rw [h2]
    rw [hf]
    all_goals ring
    all_goals linarith
  have h_eq2 : 5 * c + 8 = 12 + d := by
    linarith [eq5, eq6]
  have hc : c = 3 := by
    rw [show d = 8 + c by linarith [h_eq1]] at h_eq2
    linarith
  have h_eq3 : d = 11 := by
    rw [hc] at h_eq1
    linarith
  linarith [h_eq3]