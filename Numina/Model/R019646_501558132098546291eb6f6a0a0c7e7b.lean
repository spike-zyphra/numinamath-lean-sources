import Mathlib

theorem algebra_223775 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b)
    (h : ∀ n, f^[n + 1] = f ∘ f^[n]) (h7 : ∀ x, f^[7] x = 128 * x + 381) :
    a + b = 5 := by

  have f1 : ∀ x, f x = a * x + b := by 
    intro x
    simpa using hf x

  have f2 : ∀ x, f^[2] x = a^2 * x + b * (a + 1) := by 
    intro x
    have h1 : f^[2] x = f (f x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f1, f1]
    ring

  have f3 : ∀ x, f^[3] x = a^3 * x + b * (a^2 + a + 1) := by 
    intro x 
    have h1 : f^[3] x = f (f^[2] x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f2, f1]
    ring

  have f4 : ∀ x, f^[4] x = a^4 * x + b * (a^3 + a^2 + a + 1) := by 
    intro x 
    have h1 : f^[4] x = f (f^[3] x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f3, f1]
    ring

  have f5 : ∀ x, f^[5] x = a^5 * x + b * (a^4 + a^3 + a^2 + a + 1) := by 
    intro x 
    have h1 : f^[5] x = f (f^[4] x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f4, f1]
    ring

  have f6 : ∀ x, f^[6] x = a^6 * x + b * (a^5 + a^4 + a^3 + a^2 + a + 1) := by
    intro x 
    have h1 : f^[6] x = f (f^[5] x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f5, f1]
    ring

  have f7 : ∀ x, f^[7] x = a^7 * x + b * (a^6 + a^5 + a^4 + a^3 + a^2 + a + 1) := by 
    intro x 
    have h1 : f^[7] x = f (f^[6] x) := by 
      simp [Function.iterate_succ_apply']
    rw [h1, f6, f1]
    ring

  have eq1 := h7 0 
  rw [f7 0] at eq1 
  have eq2 := h7 1 
  rw [f7 1] at eq2 
  have eq3 : a^7 = 128 := by 
    nlinarith 
  have ha : a = 2 := by
    have h1 : a^7 - 128 = 0 := by 
      linarith [eq3]
    have h2 : a^7 - 128 = (a - 2) * (a^6 + 2 * a^5 + 4 * a^4 + 8 * a^3 + 16 * a^2 + 32 * a + 64) := by ring
    rw [h2] at h1 
    cases' (mul_eq_zero.1 h1) with h3 h4 
    · -- Case a - 2 = 0.
      linarith
    · -- Case a^6 + 2*a^5 + 4*a^4 + 8*a^3 + 16*a^2 + 32*a + 64 = 0.
      nlinarith [sq_nonneg (a^3 + a^2 * 2 + a * 4 + 8), sq_nonneg (a^2 + 2 * a + 4), sq_nonneg (a + 2), sq_nonneg (a - 2)
      ]

  rw [ha] at eq1 
  have hb : b = 3 := by 
    nlinarith
  rw [ha, hb]
  norm_num