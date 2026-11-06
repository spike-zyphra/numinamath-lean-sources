import Mathlib

theorem algebra_6346 (x : ℝ) : ∑ i ∈ Finset.range 2019, (2 * x + (i + 1)) / (i + 2) = 4038 * x ↔ x = 1 / 2 := by
  constructor
  · -- Assume $\sum_{i \in range 2019} \frac{2 * x + (i + 1)}{i + 2} = 4038 * x$ prove $x = 1/2$
    intro h
    have h1 : ∑ i in Finset.range 2019, (2 * x + (i + 1)) / (i + 2) = 4038 * x := h
    have h2 : x = 1 / 2 := by
      have h3 : ∑ i in Finset.range 2019, (2 * x + (i + 1) ) / (i + 2) = (2 * x - 1) * (∑ i in Finset.range 2019, (1 / ((i : ℝ) + 2))) + 2019 := by
        have h4 : ∀ i : ℕ, i ∈ Finset.range 2019 → (2 * x + (i + 1) ) / ((i : ℝ) + 2) = (2 * x - 1) * (1 / ((i : ℝ) + 2)) + 1 := by
          intro i hi
          field_simp
          <;> ring
        rw [Finset.sum_congr rfl (fun i hi => h4 i hi)]
        have h5 : ∑ i in Finset.range 2019, ((2 * x - 1) * (1 / ((i : ℝ) + 2)) + 1) = (2 * x - 1) * (∑ i in Finset.range 2019, (1 / ((i : ℝ) + 2))) + 2019 := by
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum]
          simp [Finset.sum_const, Finset.card_range]
          <;> ring
          all_goals norm_num
        linarith [h5]
      rw [h3] at h1
      norm_num [Finset.sum_range_succ] at h1 ⊢
      <;> nlinarith
    exact h2
  · -- Assume $x = 1/2$ prove $\sum_{i \in range 2019} \frac{2 * x + (i + 1)}{i + 2} = 4038 * x$
    intro h
    rw [h]
    have h1 : ∑ i in Finset.range 2019, (2 * (1 / 2 : ℝ) + (i + 1) ) / (i + 2) = 4038 * (1 / 2 : ℝ) := by
      have h3 : ∑ i in Finset.range 2019, (2 * (1 / 2 : ℝ) + (i + 1) ) / (i + 2) = 2019 := by
        have h4 : ∀ i : ℕ, i ∈ Finset.range 2019 → (2 * (1 / 2 : ℝ) + (i + 1) ) / (i + 2) = 1 := by
          intro i hi
          field_simp
          <;> ring
        rw [Finset.sum_congr rfl (fun i hi => h4 i hi)]
        norm_num [Finset.sum_const, Finset.card_range]
      rw [h3]
      all_goals norm_num
    exact h1