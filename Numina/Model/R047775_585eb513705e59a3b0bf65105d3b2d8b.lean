import Mathlib

theorem algebra_12151 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n > 0, a (n + 1) = 2 * (n + 2) / (n + 1) * a n) :
    a 2014 / (∑ i in Finset.Icc 1 2013, a i) = 2015 / 2013 := by

  have h5 : ∀ (n : ℕ), a (n + 1) = (n + 2) * (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have eq3 : a (n + 2) = (2 * ((↑n + 1 + 2) ) / (↑n + 1 + 1) ) * a (n + 1) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq3]
      rw [ih]
      field_simp at *
      ring_nf

  have h6 : ∀ (N : ℕ), ∑ i in Finset.Icc 1 N, a i = (N : ℝ) * (2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero =>
      norm_num [Finset.sum_eq_zero]
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      have eq7 : a (N + 1) = (N + 2) * (2 : ℝ) ^ N := by
        specialize h5 N
        norm_num at h5 ⊢
        linarith
      rw [eq7]
      rw [ih]
      field_simp at *
      ring_nf

  have ha2014 : a 2014 = (2015 : ℝ) * (2 : ℝ) ^ 2013 := by
    have h7 : a 2014 = (2014 + 1) * (2 : ℝ) ^ 2013 := by
      specialize h5 2013
      norm_num at h5 ⊢
      linarith
    nlinarith

  have h8 : ∑ i in Finset.Icc 1 2013, a i = (2013 : ℝ) * (2 : ℝ) ^ 2013 := by
    specialize h6 2013
    norm_num at h6 ⊢
    nlinarith

  rw [ha2014, h8]
  field_simp
  <;> ring_nf <;> norm_num