import Mathlib

theorem algebra_629591 {a : ℕ → ℝ} (ha : a 4 = 1 ∧ a 11 = 9)
    (hsum : ∀ n, a n + a (n + 1) + a (n + 2) = 15) :
    a 2016 = 5 := by
  rcases ha with ⟨ha4, ha11⟩
  have h1 : ∀ n, a (n + 3) = a n := by
    intro n
    have eq1 := hsum n
    have eq2 := hsum (n + 1)
    simp [show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega] at eq2 ⊢
    linarith [eq1, eq2]

  have h2 : a 2016 = a 6 := by
    have h3 : ∀ (k : ℕ), a (6 + 3 * k) = a 6 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        have eq1 : 6 + 3 * (k + 1) = (6 + 3 * k) + 3 := by
          ring_nf
        rw [eq1]
        have eq2 : a ((6 + 3 * k) + 3) = a (6 + 3 * k) := by
          apply h1
        rw [eq2, ih]
    specialize h3 670
    norm_num at h3 ⊢
    linarith [h3]

  have h_a7 : a 7 = 1 := by
    have eq4 := hsum 4
    have eq5 := hsum 5
    norm_num [ha4] at eq4
    linarith [eq4, eq5]

  have h_a8 : a 8 = 9 := by
    have eq6 := hsum 7
    have eq7 := hsum 8
    have eq8 := hsum 9
    have eq9 := hsum 10
    have eq10 := hsum 11
    have eq11 := hsum 12
    norm_num [h_a7, ha11] at eq6 eq7 eq8 eq9 eq10 eq11
    linarith [h_a7, ha4, ha11]

  have h_a6 : a 6 = 5 := by
    have eq6 := hsum 6
    have eq7 := hsum 7
    have eq8 := hsum 8
    have eq9 := hsum 9
    have eq10 := hsum 10
    have eq11 := hsum 11
    have eq12 := hsum 12
    norm_num [h_a7, h_a8, ha4, ha11] at eq6 eq7 eq8 eq9 eq10 eq11 eq12
    linarith [h_a7, h_a8, ha4, ha11]

  rw [h2]
  linarith [h_a6]