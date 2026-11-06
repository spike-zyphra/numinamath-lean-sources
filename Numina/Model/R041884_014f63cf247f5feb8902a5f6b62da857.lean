import Mathlib

theorem algebra_241688 (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range 59, a i ∈ Set.Icc (-2) 17) (hsum : ∑ i in Finset.range 59, a i = 0) :
∑ i in Finset.range 59, (a i) ^ 2 ≤ 2006:= by
  have h1 : ∀ i ∈ Finset.range 59, -2 ≤ a i ∧ a i ≤ 17 := by
    intro i hi
    specialize ha i hi
    simpa using ha
  have h2 : ∀ i ∈ Finset.range 59, (a i) ^ 2 ≤ 15 * (a i) + 34 := by
    intro i hi 
    have h3 : -2 ≤ a i ∧ a i ≤ 17 := h1 i hi
    nlinarith [sq_nonneg (a i - 17), sq_nonneg (a i + 2)]
  have h3 : ∑ i in Finset.range 59, (a i) ^ 2 ≤ ∑ i in Finset.range 59, (15 * (a i) + 34) := by
    apply Finset.sum_le_sum 
    intro i hi 
    specialize h2 i hi
    linarith 
  have h4 : ∑ i in Finset.range 59, (15 * (a i) + 34) = 2006 := by
    have h5 : ∑ i in Finset.range 59, (15 * (a i) + 34) = 15 * (∑ i in Finset.range 59, (a i)) + 59 * 34 := by 
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      <;> ring
    rw [h5, hsum]
    all_goals norm_num 
  linarith [h3, h4]