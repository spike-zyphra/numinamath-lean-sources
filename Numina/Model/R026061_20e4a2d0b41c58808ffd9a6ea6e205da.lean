import Mathlib

theorem algebra_52101 {f g : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (hg : ∃ c d, g = fun x => c * x + d) (hfg : ∀ x, f (g x) = x ∧ g (f x) = x)
    (hf0 : f 0 = 4) (hg5 : g 5 = 17) : f 2006 = 122 := by
  rcases hf with ⟨a, b, hf_eq⟩
  rcases hg with ⟨c, d, hg_eq⟩
  have hb : b = 4 := by
    simp [hf_eq] at hf0
    linarith
  have eq1 : g 5 = c * 5 + d := by 
    simp [hg_eq]
  have eq2 : c * 5 + d = 17 := by 
    linarith [hg5, eq1]
  have h1 := hfg 0
  have h2 : g (f 0) = 0 := by 
    linarith [h1.right]
  rw [show f 0 = 4 by exact hf0] at h2
  have eq3 : g 4 = 0 := by 
    linarith 
  have eq4 : c * 4 + d = 0 := by 
    simp [hg_eq] at eq3 
    linarith
  have hc : c = 17 := by
    linarith [eq2, eq4]
  have hd : d = -68 := by
    linarith [hc, eq4]
  have h6 := (hfg 5).left
  have eq5 : f (g 5) = 5 := by
    linarith [h6]
  have eq6 : f (g 5) = a * (g 5) + b := by 
    rw [hf_eq]
  rw [eq6] at eq5
  have eq7 : g 5 = 17 := by 
    linarith [hg5]
  rw [eq7, hb] at eq5
  have ha : a = 1 / 17 := by 
    linarith 
  have h9 : f 2006 = a * (2006 : ℝ) + b := by 
    simp [hf_eq]
    <;> ring
  rw [h9]
  rw [ha, hb]
  norm_num