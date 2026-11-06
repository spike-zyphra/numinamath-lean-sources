import Mathlib

theorem number_theory_89660 (a : ℕ → ℕ)
    (h : ∀ m n, ∑ i in Finset.Icc 1 (2 * m), a (n * i) ≤ m) :
    ∃ k d, ∑ i in Finset.Icc 1 (2 * k), a (d * i) = k - 2014 := by

  have h1 : a 0 = 0 := by
    have h1 := h 1 0
    norm_num [Finset.sum_Icc_succ_top] at h1
    all_goals omega
  use 2014
  use 0
  have h2 : ∑ i in Finset.Icc 1 (2 * 2014), a (0 * i) = 0 := by
    have h3 : ∀ i, i ∈ Finset.Icc 1 (2 * 2014) → a (0 * i) = 0 := by
      intro i hi
      have h4 : a (0 * i) = 0 := by
        have h5 : (0 * i) = 0 := by
          omega
        rw [h5]
        omega
      tauto
    apply Finset.sum_eq_zero
    intro i hi
    specialize h3 i hi
    tauto
  omega