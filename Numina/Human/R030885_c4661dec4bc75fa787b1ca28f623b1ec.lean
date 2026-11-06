import Mathlib

/- Let $a,b,c,d,e,f$ be positive numbers such that $a,b,c,d$ is an arithmetic progression, and $a,e,f,d$ is a geometric progression. Prove that $bc\ge ef$. -/
theorem inequalities_75556 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (h1 : ∃ d' : ℝ, b = a + d' ∧ c = b + d' ∧ d = c + d')
    (h2 : ∃ r : ℝ, e = a * r ∧ f = e * r ∧ d = f * r) :
    b * c ≥ e * f := by 
  obtain ⟨d', h1⟩ := h1  -- Unpack arithmetic progression condition
  obtain ⟨r, h2⟩ := h2   -- Unpack geometric progression condition
  nlinarith [sq_nonneg d'] -- Suppose and prove directly independent satisfaction