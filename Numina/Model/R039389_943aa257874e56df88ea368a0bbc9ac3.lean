import Mathlib

theorem algebra_246734 (x : ℕ → ℝ) (hx : ∀ i ∈ Finset.range 1996, x i > 0)
    (h0 : x 0 = x 1995) (h : ∀ i ∈ Finset.Icc 1 1995, x i + 2 / x (i - 1) = 2 * x i + 1 / x i) :
    x 0 ≤ 2 ^ 997 := by

  have h1 : ∀ i ∈ Finset.Icc 1 1995, x (i - 1) ≤ 1 := by
    intro i hi
    have h2 := h i hi
    have hx1 : x (i - 1) > 0 := by
      have h21 : (i - 1) ∈ Finset.range 1996 := by
        simp at *
        all_goals omega
      apply hx (i - 1) h21
    have hx2 : x i > 0 := by
      have h21 : i ∈ Finset.range 1996 := by
        simp at *
        all_goals omega
      apply hx i h21

    have eq2 : 2 / x (i - 1) = x i + 1 / x i := by
      have h4 : x i + 2 / x (i - 1) = 2 * x i + 1 / x i := h2
      field_simp at h4 ⊢
      nlinarith

    have h5 : x i + 1 / x i ≥ 2 := by
      have hx3 : x i > 0 := hx2
      have h6 : x i + 1 / x i - 2 ≥ 0 := by
        have h7 : x i + 1 / x i - 2 = (x i ^ 2 - 2 * x i + 1) / x i := by
          field_simp
          ring
        rw [h7]
        have h8 : x i ^ 2 - 2 * x i + 1 ≥ 0 := by
          have h9 : x i ^ 2 - 2 * x i + 1 = (x i - 1) ^ 2 := by ring
          rw [h9]
          positivity
        have h10 : (x i ^ 2 - 2 * x i + 1) / x i ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith

    have h7 : 2 / x (i - 1) ≥ 2 := by
      linarith [eq2, h5]

    have h8 : x (i - 1) ≤ 1 := by
      by_contra h
      push_neg at h
      have h9 : x (i - 1) > 1 := by linarith
      have h10 : 2 / x (i - 1) < 2 := by
        have h11 : x (i - 1) > 1 := h9
        have h12 : 1 / x (i - 1) < 1 := by
          apply (div_lt_iff₀ (by linarith)).mpr
          linarith
        have h13 : 2 / x (i - 1) = 2 * (1 / x (i - 1)) := by ring
        nlinarith
      linarith
    linarith

  have hx0 : x 0 ≤ 1 := by
    have h10 := h1 1 (by norm_num)
    norm_num at h10 ⊢
    linarith

  have h2 : (2 : ℝ) ^ 997 ≥ (1 : ℝ) := by
    norm_num

  nlinarith [hx0, h2]