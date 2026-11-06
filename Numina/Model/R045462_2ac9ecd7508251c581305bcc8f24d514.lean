import Mathlib

theorem algebra_109813 (x : ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, a n = 1 + x ^ (n + 1) + x ^ (n + 2)) (h : a 2 ^ 2 = a 1 * a 3) :
    ∀ n ≥ 3, a n ^ 2 = a (n - 1) * a (n + 1) := by

  have eq1 : a 1 = 1 + x ^ 2 + x ^ 3 := by
    specialize ha 1
    norm_num at ha ⊢
    linarith

  have eq2 : a 2 = 1 + x ^ 3 + x ^ 4 := by
    specialize ha 2
    norm_num at ha ⊢
    linarith

  have eq3 : a 3 = 1 + x ^ 4 + x ^ 5 := by
    specialize ha 3
    norm_num at ha ⊢
    linarith

  rw [eq2] at h
  rw [eq1, eq3] at h

  have eq5 : (x - 1)^2 * (x + 1) * x^2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x * (x - 1)), sq_nonneg (x * (x + 1)), sq_nonneg ((x - 1) * (x + 1))]
  
  cases' (mul_eq_zero.mp eq5) with eq6 eq7
  · cases' (mul_eq_zero.mp eq6) with eq8 eq9

    · -- $(x - 1)^2 = 0$.
      have hx1 : x = 1 := by
        have h10 : (x - 1) ^ 2 = 0 := eq8
        have h11 : x - 1 = 0 := by
          apply pow_eq_zero
          exact h10
        linarith

      intro n hn
      have h5 : a n = 3 := by
        rw [ha n]
        rw [hx1]
        norm_num

      have h6 : a (n - 1) = 3 := by
        rw [ha (n - 1)]
        rw [hx1]
        norm_num

      have h7 : a (n + 1) = 3 := by
        rw [ha (n + 1)]
        rw [hx1]
        norm_num

      rw [h5, h6, h7]
      all_goals nlinarith

    · -- $(x + 1) = 0$.
      have hx2 : x = -1 := by
        linarith

      intro n hn
      have h5 : a n = 1 := by
        rw [ha n]
        rw [hx2]
        ring_nf

      have h6 : a (n - 1) = 1 := by
        rw [ha (n - 1)]
        rw [hx2]
        ring_nf

      have h7 : a (n + 1) = 1 := by
        rw [ha (n + 1)]
        rw [hx2]
        ring_nf

      rw [h5, h6, h7]
      all_goals nlinarith

  · -- $x^2 = 0$.
    have hx3 : x = 0 := by
      have h10 : x ^ 2 = 0 := eq7
      have h11 : x = 0 := by
        apply pow_eq_zero
        exact h10
      linarith

    intro n hn
    have h5 : a n = 1 := by
      rw [ha n]
      rw [hx3]
      norm_num

    have h6 : a (n - 1) = 1 := by
      rw [ha (n - 1)]
      rw [hx3]
      norm_num

    have h7 : a (n + 1) = 1 := by
      rw [ha (n + 1)]
      rw [hx3]
      norm_num

    rw [h5, h6, h7]
    all_goals nlinarith