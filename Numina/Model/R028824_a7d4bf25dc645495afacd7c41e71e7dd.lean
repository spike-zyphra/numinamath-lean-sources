import Mathlib

theorem algebra_21247 {a g : ℕ+ → ℝ} (ha : ∃ d, ∀ n, a n = a 1 + d * (n.val - 1))
    (hg : ∃ r, ∀ n, g n = g 1 * r ^ (n.val - 1)) (h1 : a 1 + g 1 = 0) (h2 : a 2 + g 2 = 0)
    (h3 : a 3 + g 3 = 1) (h4 : a 4 + g 4 = 0) :
    a 5 + g 5 = 3 := by
  rcases ha with ⟨d, had⟩
  rcases hg with ⟨r, hg⟩
  have eq2 : a 2 = a 1 + d := by
    specialize had 2
    norm_num at had
    linarith
  have eq3 : a 3 = a 1 + 2 * d := by 
    specialize had 3 
    norm_num at had 
    linarith
  have eq4 : a 4 = a 1 + 3 * d := by 
    specialize had 4 
    norm_num at had 
    linarith
  have eq5 : a 5 = a 1 + 4 * d := by 
    specialize had 5 
    norm_num at had 
    linarith
  have eqg2 : g 2 = g 1 * r ^ 1 := by
    specialize hg 2
    simpa using hg
  have eqg3 : g 3 = g 1 * r ^ 2 := by
    specialize hg 3 
    simpa using hg 
  have eqg4 : g 4 = g 1 * r ^ 3 := by 
    specialize hg 4 
    simpa using hg 
  have eqg5 : g 5 = g 1 * r ^ 4 := by 
    specialize hg 5 
    simpa using hg 
  simp [eq2, eqg2] at h2 
  simp [eq3, eqg3] at h3
  simp [eq4, eqg4] at h4 
  simp [eq5, eqg5] at *
  nlinarith [sq_nonneg (r + 2), sq_nonneg (g 1 - 1 / 9), sq_nonneg (a 1 + 1 / 9), sq_nonneg (d - 1 / 3), sq_nonneg (r + 2)]