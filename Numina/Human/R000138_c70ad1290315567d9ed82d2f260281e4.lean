import Mathlib

/- a) \( \sum_{j=1}^{10} 2 \)-/
theorem number_theory_4790_1 : ∑ j in Finset.range 10, 2 = 20 := by
  -- verify by computation
  simp

/- b) \( \sum_{j=1}^{10} j \)-/
theorem number_theory_4790_2 : ∑ j in Finset.range 10, (j + 1) = 55 := by
  -- verify by computation
  simp [Finset.sum_range_succ]

/- c) \( \sum_{j=1}^{10} j^{2} \)-/
theorem number_theory_4790_3 : ∑ j in Finset.range 10, (j + 1) ^ 2 = 385 := by
  -- verify by computation
  simp [Finset.sum_range_succ]

/- d) \( \sum_{j=1}^{10} 2^{j} \)-/
theorem number_theory_4790_4 : ∑ j in Finset.range 10, (2 : ℤ) ^ (j + 1) = 2046 := by
  -- verify by computation
  simp [Finset.sum_range_succ]
