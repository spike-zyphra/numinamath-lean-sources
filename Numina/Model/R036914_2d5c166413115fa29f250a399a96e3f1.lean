import Mathlib

theorem algebra_115482 {f : ℝ → ℝ} (hf : ∃ a b c d, f = fun x => a*x^3 + b*x^2 + c*x + d)
    (h0 : f 0 = 1) (h1 : f 1 = 1) (h2 : f 2 = 3) (h3 : f 3 = 19) :
    ∀ n, ∑ k in Finset.range (n + 1), f k = ((n + 1) * (3 * n^3 - 7 * n^2 + 4 * n + 6)) / 6 := by
  obtain ⟨a, b, c, d, hf⟩ := hf
  have eq1 : f 0 = a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d := by simp [hf]
  rw [eq1] at h0
  have eq2 : f 1 = a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d := by simp [hf]
  rw [eq2] at h1
  have eq3 : f 2 = a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d := by simp [hf]
  rw [eq3] at h2
  have eq4 : f 3 = a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d := by simp [hf]
  rw [eq4] at h3
  have ha : a = 2 := by 
    linarith 
  have hb : b = -5 := by 
    linarith
  have hc : c = 3 := by 
    linarith
  have hd : d = 1 := by 
    linarith
  intro n
  have h4 : ∀ k, f k = 2 * k ^ 3 - 5 * k ^ 2 + 3 * k + 1 := by 
    intro k
    have eq5 : f k = a * k^3 + b * k^2 + c * k + d := by
      simp [hf]
    rw [eq5]
    rw [ha, hb, hc, hd]
    all_goals ring
  have h5 : ∀ n, ∑ k in Finset.range (n + 1), f k = ((n + 1) * (3 * n^3 - 7 * n^2 + 4 * n + 6)) / 6 := by 
    intro n 
    induction n with
    | zero =>
      simp [h4]
      all_goals norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      simp [h4]
      all_goals field_simp
      all_goals ring_nf
  specialize h5 n 
  simpa using h5