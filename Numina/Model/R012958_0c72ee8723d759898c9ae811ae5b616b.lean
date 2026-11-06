import Mathlib

theorem algebra_263375 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + x * y + 1)
    (h' : f (-2) = -2) :
    {t : ℤ | f t = t} = {1, -2} := by
  have f0 : f (0 : ℝ) = -1 := by
    have h00 := h 0 0
    norm_num at h00 ⊢
    linarith
  have hf1 : f (-1 : ℝ) = -2 := by 
    have h2 := h (-1 : ℝ) (-1 : ℝ)
    norm_num at h2 ⊢
    linarith [h']
  have hf2 : f 1 = 1 := by
    have h01 := h 1 (-1 : ℝ)
    norm_num [show f (-1 : ℝ) = -2 by linarith [hf1], f0] at h01 ⊢
    linarith
  -- The general solution is f(t) = (t^2 + 3*t - 2)/2
  have f_eq : ∀ (t : ℤ), f t = (t ^ 2 + 3 * t - 2) / 2 := by
    intro t
    induction t using Int.induction_on with
    | hz => 
      norm_num [show f (0 : ℝ) = -1 by linarith [f0]]
    | hp t ih => 
      have eq5 : f ((t + 1 : ℤ) : ℝ) = f ((t : ℤ) : ℝ) + (t : ℝ) + 2 := by
        specialize h ((t : ℤ) : ℝ) (1 : ℝ)
        norm_num at h ⊢
        linarith [hf2]
      rw [eq5, ih]
      field_simp at *
      ring_nf
      <;> norm_num
      <;> ring
      all_goals linarith
    | hn t ih => 
      have eq3 : f ((-t - 1 : ℤ) : ℝ) = f ((-t : ℤ) : ℝ) - (-t : ℝ) - 1 := by
        have eq4 : f ((-t - 1 : ℤ) : ℝ) = f ((-t : ℤ) : ℝ) + f (-1 : ℝ) + ((-t : ℝ) * (-1 : ℝ)) + 1 := by
          specialize h ((-t : ℤ) : ℝ) (-1 : ℝ)
          simpa using h
        rw [eq4]
        have hf1' : f (-1 : ℝ) = -2 := by linarith [hf1]
        rw [hf1']
        ring_nf
      rw [eq3, ih]
      field_simp at *
      ring_nf
      <;> norm_num
      <;> ring
      all_goals linarith
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume f t = t, prove t = 1 or t = -2
    intro h_eq
    have eq1' : f t = (t : ℝ) := by
      exact_mod_cast h_eq
    rw [f_eq t] at eq1'
    have eq2 : (t : ℝ) ^ 2 + 3 * (t : ℝ) - 2 = 2 * (t : ℝ) := by
      have eq3 : (t^2 + 3 * t - 2 : ℝ) / 2 = (t : ℝ) := by
        linarith [eq1']
      have eq4 : (t^2 + 3 * t - 2 : ℝ) = 2 * (t : ℝ) := by
        linarith [eq3]
      nlinarith
    have eq3 : t^2 + 3 * t - 2 = 2 * t := by
      exact_mod_cast eq2
    have eq4 : t^2 + t - 2 = 0 := by
      nlinarith
    have : (t - 1) * (t + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h1 h2
    · -- $t - 1 = 0$, so $t = 1$
      left
      linarith
    · -- $t + 2 = 0$, so $t = -2$
      right
      linarith
  · -- Assume t = 1 or t = -2, prove f t = t
    rintro (h_eq | h_eq)
    · -- t = 1
      rw [h_eq]
      norm_num [hf2, f_eq]
    · -- t = -2
      rw [h_eq]
      norm_num [h', f_eq]