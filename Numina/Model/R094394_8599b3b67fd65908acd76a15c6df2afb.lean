import Mathlib

theorem algebra_277044 {f : ℝ → ℝ} (p q : ℝ) (hf : ∀ x, f x = p * x + q)
    (hff : ∀ x, f (f (f x)) = 8 * x + 21) : p + q = 5 := by
  have eq1 := hff 0
  simp [hf] at eq1
  have eq2 := hff 1
  simp [hf] at eq2
  have eq3 := hff 2
  simp [hf] at eq3
  have eq4 := hff 3
  simp [hf] at eq4
  have hp : p = 2 := by 
    have h1 : p^3 = 8 := by 
      nlinarith [eq1, eq2, eq3]
    have h2 : p^3 - 8 = 0 := by 
      linarith 
    have h3 : (p - 2) * (p^2 + 2 * p + 4) = 0 := by 
      ring_nf at h2 ⊢
      linarith 
    cases' (mul_eq_zero.mp h3) with hp1 hp2
    · -- Case p - 2 = 0, so p = 2
      linarith 
    · -- Case p^2 + 2*p + 4 = 0
      have h4 : p^2 + 2 * p + 4 > 0 := by 
        nlinarith [sq_nonneg (p + 1)]
      nlinarith 
  have hq : q = 3 := by 
    rw [hp] at eq1 
    nlinarith 
  linarith [hp, hq]