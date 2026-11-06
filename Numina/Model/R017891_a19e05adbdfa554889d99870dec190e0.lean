import Mathlib

theorem number_theory_159176 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p * q + p ^ 2 + q ^ 2 = 199) (h1 : p < q) :
    ∑ i ∈ Finset.Ico p q, (2 / ((i * (i + 1)) : ℚ)) = 11 / 13 := by

  have h2 : p ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h3 : p > 8 := h2
    have h4 : q > 8 := by linarith [show p < q from h1, h3]
    nlinarith [show p ≥ 9 by linarith, show q ≥ 9 by linarith, 
        hp.two_le, hq.two_le, 
        sq_nonneg (p - q : ℤ), 
        sq_nonneg (p + q : ℤ)
    ]

  have h3 : p < 8 := by
    by_contra h2
    push_neg at h2
    have h3 : p ≥ 8 := by linarith
    have h4 : q > 8 := by linarith [show p < q from h1, h3]
    nlinarith [show p ≥ 8 by linarith, show q ≥ 9 by linarith, 
        hp.two_le, hq.two_le, 
        sq_nonneg (p - q : ℤ), 
        sq_nonneg (p + q : ℤ)
    ]

  have h4 : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> norm_num at hp ⊢ <;> tauto

  rcases h4 with (rfl | rfl | rfl | rfl)

  · -- case p = 2
    have h5 : q = 13 := by
      have h6 : q ≤ 16 := by
        nlinarith [h]
      interval_cases q <;> norm_num at h hq ⊢
    rw [h5]
    norm_num [Finset.sum_Ico_succ_top]

  · -- case p = 3
    exfalso
    have h5 : q ≤ 30 := by
      nlinarith [h]
    interval_cases q <;> norm_num at h hq ⊢

  · -- case p = 5
    exfalso
    have h5 : q ≤ 30 := by
      nlinarith [h]
    interval_cases q <;> norm_num at h hq ⊢

  · -- case p = 7
    exfalso
    have h5 : q ≤ 30 := by
      nlinarith [h]
    interval_cases q <;> norm_num at h hq ⊢