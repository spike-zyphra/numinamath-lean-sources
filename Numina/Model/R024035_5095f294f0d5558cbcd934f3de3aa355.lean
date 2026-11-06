import Mathlib

theorem algebra_298917 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n > 0, a (n + 1) = 2 * (n + 2) / (n + 1) * a n) :
    a 2014 / ∑ i in Finset.Icc 1 2013, a i = 2015 / 2013 := by
  have h1 : ∀ (n : ℕ), a (n + 1) = 2 ^ n * (n + 2) := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have h1 : a ((n + 1) + 1) = 2 * (n + 1 + 2) / (n + 1 + 1) * a (n + 1) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [h1, ih]
      field_simp at *
      ring_nf
  have h2 : ∀ (N : ℕ), ∑ i in Finset.Icc 1 N, a i = (N : ℝ) * (2 ^ N) := by
    intro N
    induction N with
    | zero =>
      simp [Finset.sum_eq_zero]
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [h1 N]
      rw [ih]
      field_simp at *
      ring_nf
  have ha2014 : a 2014 = (2 ^ 2013 : ℝ) * (2015 : ℝ) := by
    specialize h1 2013
    norm_num at h1 ⊢
    linarith
  have ha2013sum : ∑ i in Finset.Icc 1 2013, a i = (2013 : ℝ) * (2 ^ 2013 : ℝ) := by
    specialize h2 2013
    simpa using h2
  rw [ha2014, ha2013sum]
  field_simp
  ring_nf