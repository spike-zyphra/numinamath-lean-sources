import Mathlib


theorem algebra_243538
  (t : ℕ → ℝ)
  (ht : ∀ n, n > 0 → t n = (1 / (n + 1)) / (n + 2)):
  t 1 = 1/2 - 1/3 ∧ t 2 = 1/3 - 1/4 ∧ (∑ i ∈ Finset.Icc 1 2013, t i) = 1/2 - 1/2015 := by

  have ht1 : t 1 = 1/(2:ℝ) - 1/3 := by
    rw [ht]
    push_cast
    linarith
    norm_num

  have ht2 : t 2 = 1/(3:ℝ) - 1/4 := by
    rw [ht]
    push_cast
    linarith
    norm_num

  refine ⟨ht1, ht2, ?_⟩

  have ht_sum : ∀ n, (∑ i ∈ Finset.Icc 1 n, t i) = 1/2 - 1/(n+2) := by
    intro n
    induction' n with _ hd
    . simp
    . rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [hd]
      rw [ht]
      push_cast
      field_simp
      ring_nf
      linarith

  have := ht_sum 2013
  push_cast at this
  norm_num at this
  norm_num
  exact this
