import Mathlib

theorem algebra_186509 {a : ℕ → ℕ}
    (h_arth : ∃ d : ℕ, ∀ i : ℕ, a i = a 0 + i * d)
    (h1 : ∏ i ∈ Finset.range 3, a i = 6)
    (h2 : ∏ i ∈ Finset.range 4, a i = 24) :
    a = fun x => x + 1 := by
  have h_a3 : a 3 = 4 := by
    rw [Finset.range_eq_Ico] at h1 h2
    rw [Finset.prod_Ico_succ_top zero_le_three, h1] at h2
    linarith only [h2]
  obtain ⟨d, h⟩ := h_arth
  have h_d : d = 1 := by
    rw [h] at h_a3
    have : d ≤ 1 := by omega
    interval_cases d
    . have h_a0 : a 0 = 4 := by omega
      simp [h_a0] at h
      norm_num [h] at h1
    . rfl
  have h_a0 : a 0 = 1 := by
    linarith only [h 3, h_a3, h_d]
  ext x
  rw [h x, h_a0, h_d, mul_one, add_comm]