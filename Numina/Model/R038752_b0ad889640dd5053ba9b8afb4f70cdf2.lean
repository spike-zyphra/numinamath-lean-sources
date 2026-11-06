import Mathlib

theorem algebra_13061 (f : ℝ → ℝ) (h : ∀ x y, x > 0 → y > 0 → f x * f y = f (x * y) + 2005 * (1 / x + 1 / y + 2004)) : ∃(S : Finset ℝ), S = {z | f 2 = z} ∧ S.card * (∑ z ∈ S, z) = 4011/2 := by
  have eq1 := h 1 1 (by norm_num) (by norm_num)
  norm_num at eq1
  have eq2 : (f 1 - 2006) * (f 1 + 2005) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq2) with h1 h2
  · -- If f 1 = 2006, then we can prove that f x = 1/x + 2005
    have eq3 : f 1 = 2006 := by linarith
    have eq4 : ∀ x > 0, f x = 1 / x + 2005 := by
      intro x hx
      have h2 := h x 1 hx (by norm_num)
      rw [eq3] at h2
      field_simp at h2 ⊢
      nlinarith
    have eq5 : f 2 = 4011 / 2 := by
      specialize eq4 2 (by norm_num)
      norm_num at eq4 ⊢
      linarith
    have : {z | f 2 = z} = {4011 / 2} := by
      ext z
      simp [eq5]
    use {4011 / 2}
    constructor
    · -- Show that S = {z | f 2 = z}
      ext z
      simp [this]
    · -- Show that S.card * (∑ z ∈ S, z) = 4011 / 2
      simp
  · -- Assume f 1 = -2005, show contradiction
    have eq3 : f 1 = -2005 := by linarith
    have eq4 : ∀ x > 0, f x = -2005 / 2006 * (1 / x + 2005) := by
      intro x hx
      have h2 := h x 1 hx (by norm_num)
      rw [eq3] at h2
      field_simp at h2 ⊢
      nlinarith
    -- Let's get a contradiction by using x = 2, y = 3.
    have eq5 := h 2 3 (by norm_num) (by norm_num)
    have eq6 : f 2 = -2005 / 2006 * (1 / (2 : ℝ) + 2005) := by
      apply eq4 2
      norm_num
    have eq7 : f 3 = -2005 / 2006 * (1 / (3 : ℝ) + 2005) := by
      apply eq4 3
      norm_num
    have eq8 : f 6 = -2005 / 2006 * (1 / (6 : ℝ) + 2005) := by
      have hx6 : (6 : ℝ) > 0 := by norm_num
      apply eq4 6
      exact hx6
    have eq9 : (2 : ℝ) * (3 : ℝ) = (6 : ℝ) := by norm_num
    rw [eq9] at eq5
    rw [eq6, eq7, eq8] at eq5
    norm_num at eq5
    all_goals
      nlinarith