import Mathlib

theorem algebra_309701 {A B C : ℝ} (z1 z2 z3 : ℂ)
    (hz1 : z1 = Complex.exp (Complex.I * A)) (hz2 : z2 = Complex.exp (Complex.I * B))
    (hz3 : z3 = Complex.exp (Complex.I * C)) (hsum : z1 + z2 + z3 = 0) :
    Complex.cos (A - B) = -1 / 2 := by

  have h1 : z1 + z2 = -z3 := by
    calc
      z1 + z2 = (z1 + z2 + z3) - z3 := by ring
      _ = 0 - z3 := by rw [hsum]
      _ = -z3 := by ring

  rw [hz1, hz2, hz3] at h1

  have h_eq1 : Complex.exp (Complex.I * A) + Complex.exp (Complex.I * B) = - Complex.exp (Complex.I * C) := h1

  have h2 : Complex.normSq (Complex.exp (Complex.I * A) + Complex.exp (Complex.I * B)) = Complex.normSq (- Complex.exp (Complex.I * C)) := by
    rw [h_eq1]

  have h4 : Complex.normSq (- Complex.exp (Complex.I * C)) = 1 := by
    have h6 : Complex.normSq (- Complex.exp (Complex.I * C)) = Complex.normSq (Complex.exp (Complex.I * C)) := by
      simp [Complex.normSq]
    rw [h6]
    simp [Complex.normSq, Complex.exp_re, Complex.exp_im]
    all_goals
      ring_nf
      <;> simp [Real.sin_sq, Real.cos_sq] 
      all_goals nlinarith

  have h5 : Complex.normSq (Complex.exp (Complex.I * A) + Complex.exp (Complex.I * B)) = 2 + 2 * Real.cos (A - B) := by
    simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.exp_re, Complex.exp_im]
    have eq2 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    have eq3 : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
    have eq4 : Real.cos A * Real.cos B + Real.sin A * Real.sin B = Real.cos (A - B) := by
      rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, sq_nonneg (Real.sin A - Real.sin B), sq_nonneg (Real.cos A - Real.cos B)]

  rw [h5] at h2
  rw [h4] at h2

  have h3 : Real.cos (A - B) = -1 / 2 := by
    nlinarith

  have h8 : Complex.cos (A - B) = ↑ (Real.cos (A - B)) := by 
    simp [Complex.cos]

  rw [h8]
  exact_mod_cast h3