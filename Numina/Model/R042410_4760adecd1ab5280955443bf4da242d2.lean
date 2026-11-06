import Mathlib

theorem algebra_214099 (f : ℝ → ℝ) (m n : ℝ) (hf : f = fun x => x^2 - (m - n) * x + n)
    (hvertex : ∀ x, f x = (x - 2)^2 + 3) : f (m - n) = 7 := by 
  have h1 := hvertex 0 
  simp [hf] at h1 
  have hn : n = 7 := by linarith
  have h2 := hvertex 1 
  simp [hf] at h2 
  have hm : m = 11 := by 
    rw [hn] at h2 
    linarith 
  have eq1 : f (m - n) = ((m - n) - 2)^2 + 3 := by 
    specialize hvertex (m - n)
    simpa using hvertex 
  rw [eq1]
  rw [show m = 11 by linarith [hm] ] 
  rw [show n = 7 by linarith [hn] ]
  norm_num