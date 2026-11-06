import Mathlib

theorem algebra_178201 {a : ℕ → ℝ} (h : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha : a 0 = 3) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by

  have h1 : ∀ (n : ℕ), a n ≠ 0 := by
    intro n 
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      by_contra h'
      have eq1 : (3 - a (n + 1)) * (6 + a n) = 18 := h n
      have eq2 : a (n + 1) = 0 := by linarith [h']
      have eq3 : 3 * (6 + a n) = 18 := by
        rw [show a (n + 1) = 0 by linarith [h']] at eq1 
        nlinarith 
      have eq4 : a n = 0 := by
        linarith 
      contradiction 

  have h2 : ∀ (n : ℕ), 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := by
    intro n 
    have eq5 : (3 - a (n + 1)) * (6 + a n) = 18 := h n 
    have eq6 : a n ≠ 0 := h1 n
    have eq7 : a (n + 1) ≠ 0 := h1 (n + 1)
    have eq8 : (3 - a (n + 1)) * (6 + a n) = 18 := h n 
    have eq9 : a (n + 1) * (6 + a n) = 3 * a n := by 
      nlinarith
    have h2 : a (n + 1) ≠ 0 := h1 (n + 1)
    have eq6 : a n ≠ 0 := h1 n 
    have eq10 : 1 / a (n + 1) = (6 + a n) / (3 * a n) := by 
      field_simp [h2, eq6] at eq9 ⊢
      nlinarith 
    have eq11 : (6 + a n) / (3 * a n) = 2 * (1 / a n) + 1 / 3 := by 
      field_simp [eq6]
      <;> nlinarith 
    rw [eq10]
    linarith [eq11]

  have h3 : ∀ (n : ℕ), 1 / a n = (2 ^ (n + 1) - 1) / 3 := by 
    intro n 
    induction n with 
    | zero =>
      rw [ha]
      norm_num 
    | succ n ih =>
      have h6 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := h2 n 
      rw [h6]
      rw [ih]
      field_simp at *
      ring_nf

  have h4 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [Finset.sum_range_succ, ha, h3]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h3]
      field_simp at *
      ring_nf

  specialize h4 n
  norm_num at h4 ⊢
  linarith