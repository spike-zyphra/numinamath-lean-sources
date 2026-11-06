import Mathlib

theorem algebra_199005 {f g : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (hg : ∀ x, g x = 2 ^ x * f x) (hfg : ∀ x, g (x + 1) - g x ≥ 2 ^ (x + 1) * x ^ 2)
    (hf0 : f 0 = 12) :
    f = fun x => 2 * x ^ 2 - 8 * x + 12 := by
  rcases hf with ⟨a, b, c, hfl⟩
  have hc : c = 12 := by
    simp [hfl] at hf0
    linarith
  have eq1 := hfg 0
  simp [hg, hfl, hc] at eq1
  have eq2 := hfg 1
  simp [hg, hfl, hc] at eq2
  have eq3 := hfg 2
  simp [hg, hfl, hc] at eq3
  have eq4 := hfg 3
  simp [hg, hfl, hc] at eq4
  have eq5 := hfg 4
  simp [hg, hfl, hc] at eq5
  
  -- To obtain equality from inequalities at specific points.
  have h6 := hfg (0 : ℝ)
  simp [hg, hfl, hc] at h6 
  have h7 := hfg (1 : ℝ)
  simp [hg, hfl, hc] at h7 
  have h8 := hfg (2 : ℝ)
  simp [hg, hfl, hc] at h8
  have h9 := hfg (3 : ℝ)
  simp [hg, hfl, hc] at h9 
  have h10 := hfg (4 : ℝ)
  simp [hg, hfl, hc] at h10
  
  have h11 := hfg (-1 : ℝ)
  norm_num [hg, hfl, hc] at h11
  
  have h12 := hfg (-2 : ℝ)
  norm_num [hg, hfl, hc] at h12
  
  have h13 := hfg (-3 : ℝ)
  norm_num [hg, hfl, hc] at h13
  
  have h14 := hfg (5 : ℝ)
  norm_num [hg, hfl, hc] at h14
  
  have h15 := hfg (6 : ℝ)
  norm_num [hg, hfl, hc] at h15
  
  funext x
  simp [hfl, hc]
  have ha2 : a = 2 := by 
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b + 8), sq_nonneg (x * 0), sq_nonneg ((a * b)), sq_nonneg (b - (-8)), sq_nonneg (a - 2)]
  have hb8 : b = -8 := by 
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b + 8), sq_nonneg (x * 0), sq_nonneg ((a * b)), sq_nonneg (b - (-8)), sq_nonneg (a - 2)]
  simp [ha2, hb8]
  all_goals
    nlinarith
    <;> norm_num
    <;> nlinarith
    <;> norm_num
    <;> nlinarith