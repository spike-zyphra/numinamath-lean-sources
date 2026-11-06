import Mathlib

theorem algebra_260233 {a : ℕ → ℝ} (ha1 : a 1 = 2) (han : ∀ n > 0, a (n + 1) = (2 * (n + 2)) / (n + 1) * a n) :
    a 2014 / (∑ i in Finset.Icc 1 2013, a i) = 2015 / 2013 := by

  have h2 : ∀ n : ℕ, a (n + 1) = (n + 2) * (2 ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have eq1 : a ((n + 1) + 1) = (2 * ((n + 1) + 2)) / ((n + 1) + 1) * a (n + 1) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq1]
      rw [ih]
      field_simp
      ring_nf

  have h3 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, a i = (n) * (2 ^ n) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num [Finset.sum_eq_zero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have eq1 : a (n + 1) = (n + 2) * (2 ^ n) := by
        specialize h2 n
        simpa using h2
      simp [eq1]
      ring_nf

  have eq1 : a 2014 = (2015) * (2 ^ 2013) := by
    have eq2 : a 2014 = (2014 + 1) * (2 ^ 2013) := by
      specialize h2 2013
      norm_num at h2 ⊢
      linarith
    norm_num at eq2 ⊢
    linarith

  have eq2 : ∑ i in Finset.Icc 1 2013, a i = (2013) * (2 ^ 2013) := by 
    specialize h3 2013
    norm_num at h3 ⊢
    linarith

  rw [eq1, eq2]
  field_simp
  <;> norm_num
  all_goals linarith