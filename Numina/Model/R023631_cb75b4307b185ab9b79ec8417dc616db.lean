import Mathlib

theorem algebra_13022 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f : ℂ → ℂ) (hf : ∀ z, f z = (a + b * .I) * z)
    (h : ∀ z, dist (f z) z = dist (f z) 0) (h' : Complex.abs (a + b * .I) = 8) :
    b ^ 2 = 255 / 4 := by 
  have eq1 := h 1
  simp [hf, dist_eq_norm] at eq1
  have eq2 : Complex.abs ((a + b * Complex.I) - 1) = Complex.abs (a + b * Complex.I) := by
    simpa using eq1
  have h_mod1 : Complex.abs ((a + b * Complex.I) - 1) = Real.sqrt ((a - 1) ^ 2 + b ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  have h_mod2 : Complex.abs (a + b * Complex.I) = Real.sqrt (a ^ 2 + b ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  rw [h_mod1] at eq2
  rw [h_mod2] at eq2
  have eq3 : (a - 1) ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 := by 
    have h1 : Real.sqrt ((a - 1) ^ 2 + b ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) := eq2
    have h2 : (Real.sqrt ((a - 1) ^ 2 + b ^ 2)) ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
      rw [h1]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h2
    linarith
  have eq4 : a = 1 / 2 := by 
    nlinarith
  have h_mod : Complex.abs (a + b * Complex.I) = 8 := h'
  rw [h_mod2] at h_mod
  rw [eq4] at h_mod
  have h64 : ( (1 / 2: ℝ) ) ^ 2 + b ^ 2 = 64 := by
    have h1 : Real.sqrt ( (1 / 2: ℝ) ^ 2 + b ^ 2 ) = 8 := by
      simpa using h_mod
    have h2 : (Real.sqrt ( (1 / 2: ℝ) ^ 2 + b ^ 2 )) ^ 2 = (8 : ℝ) ^ 2 := by
      rw [h1]
    rw [Real.sq_sqrt (by positivity) ] at h2
    nlinarith
  nlinarith