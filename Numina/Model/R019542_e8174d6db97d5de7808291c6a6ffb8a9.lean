import Mathlib

theorem algebra_11489 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = (x ^ 2 - 1) * (x ^ 2 + a * x + b))
    (h : ∀ x, f x = f (4 - x)) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) (-16) := by

  have eq1 : -b = 15 * (16 + 4 * a + b) := by
    have h_eq : f 0 = f (4 - (0 : ℝ)) := h 0
    simp [hf] at h_eq
    linarith

  have eq2 : 9 + 3 * a + b = 0 := by
    have h_eq1 : f 1 = f (4 - (1 : ℝ)) := h 1
    have eq3 : f 1 = 0 := by
      rw [hf 1]
      norm_num
    have eq4 : f (4 - (1 : ℝ)) = 8 * (9 + 3 * a + b) := by
      have eq5 : f (4 - (1 : ℝ)) = f 3 := by
        ring_nf
      rw [eq5]
      rw [hf 3]
      ring_nf 
    rw [eq3, eq4] at h_eq1
    cases' (mul_eq_zero.mp (show (8 : ℝ) * (9 + 3 * a + b) = 0 by linarith [h_eq1] )) with h1 h2 
    · -- Case that 8 = 0, which is impossible
      linarith
    · -- Case that 9 + 3 * a + b = 0, which is the desired result
      linarith

  have h1 : a = -8 := by
    nlinarith [eq1, eq2]

  have h2 : b = 15 := by
    nlinarith [eq1, eq2]

  constructor
  · -- Show that -16 is in the image
    use (2 + Real.sqrt 5)
    have h50 : (2 + Real.sqrt 5) ∈ (Set.univ : Set ℝ) := by 
      simp 
    have h51 : f (2 + Real.sqrt 5) = -16 := by
      have h52 : f (2 + Real.sqrt 5) = ((2 + Real.sqrt 5) ^ 2 - 1) * ((2 + Real.sqrt 5) ^ 2 + a * (2 + Real.sqrt 5) + b) := by 
        apply hf 
      rw [h52]
      rw [h1, h2]
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5)]
    exact ⟨h50, h51⟩

  · -- Show that -16 is minimal 
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    have h5 : f x = (x ^ 2 - 1) * (x ^ 2 + a * x + b) := by 
      apply hf 
    have h6 : f x ≥ -16 := by 
      have h7 : f x = (x ^ 2 - 1) * (x ^ 2 + a * x + b) := by 
        apply hf 
      rw [h7]
      rw [h1, h2]
      nlinarith [sq_nonneg (x ^ 2 - 4 * x - 1), sq_nonneg (x ^ 2 - 4 * x - 1), sq_nonneg (x - 2), mul_nonneg (sq_nonneg (x - 2)) (sq_nonneg (x - 2)), sq_nonneg (x * (x - 2)), sq_nonneg ((4 - x)^2 - 4), sq_nonneg (x^2 - 4)]
    have h8 : y = f x := by 
      linarith [hx, h5]
    linarith [h8, h6]