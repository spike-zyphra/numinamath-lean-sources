import Mathlib

theorem algebra_206594 (x : Fin 11 → ℝ) (hx : ∀ i, x i > 0)
    (h : ∀ i, x i = ∑ j in Finset.univ \ {i}, x j ^ 2) :
    ∀ i, x i = 1 / 10 := by
  have h3 : ∀ i j, x i = x j := by
    intro i j
    have eq2 := h i
    have eq3 := h j
    simp [Finset.sum_eq_add_sum_diff_singleton] at eq2 eq3
    have h4 : x i > 0 := hx i
    have h5 : x j > 0 := hx j
    nlinarith [show x i > 0 by apply hx, show x j > 0 by apply hx, sq_nonneg (x i - x j), sq_nonneg (x j - x i)]
  intro i
  have eq4 : x i = 1 / 10 := by
    have h4 := h i
    have eq6 : ∑ j in Finset.univ \ {i}, x j ^ 2 = 10 * (x i) ^ 2 := by
      have h5'1 : ∀ k, k ∉ ({i} : Finset (Fin 11)) → x k = x i := by
        intro k hk
        have eq7 : x k = x i := by
          apply h3 k i
        assumption
      have h11 : Finset.card (Finset.univ \ {i}) = 10 := by
        simp [Finset.card_sdiff, Finset.card_univ, Finset.card_singleton]
        all_goals linarith
      calc
        ∑ j in Finset.univ \ {i}, x j ^ 2 = ∑ j in Finset.univ \ {i}, (x i) ^ 2 := by
          apply Finset.sum_congr
          . rfl
          . intro j h2
            have h2' : j ≠ i := by
              simp at h2 ⊢
              assumption
            have eq8 : x j = x i := h5'1 j (by simp at h2 ⊢; tauto)
            simp [eq8]
        _ = (Finset.card (Finset.univ \ {i})) * (x i) ^ 2 := by
          rw [Finset.sum_const]
          simp
        _ = 10 * (x i) ^ 2 := by
          rw [h11]
          all_goals norm_num
    rw [eq6] at h4
    have h4'1 : x i > 0 := hx i
    have h4'2 : x i * (10 * x i - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4'2) with h4'3 h4'4
    · -- Case h4'3: x i = 0
      linarith -- contradicts x i > 0
    · -- Case h4'4: 10 * x i - 1 = 0
      linarith
  exact_mod_cast eq4