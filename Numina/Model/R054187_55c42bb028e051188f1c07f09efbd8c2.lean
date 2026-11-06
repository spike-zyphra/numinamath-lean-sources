import Mathlib

theorem algebra_297224 {a : ℕ → ℤ} (h : ∀ n ≥ 2, a (n + 1) = a n + a (n - 1)) (ha : a 7 = 8) :
    ∑ i in Finset.range 10, a (i + 1) = 88 := by
  have h3 : a 3 = a 2 + a 1 := by
    specialize h 2 (by norm_num)
    norm_num at h
    exact h
  have h4 : a 4 = a 3 + a 2 := by
    specialize h 3 (by norm_num)
    norm_num at h
    exact h
  have h5 : a 5 = a 4 + a 3 := by
    specialize h 4 (by norm_num)
    norm_num at h
    exact h
  have h6 : a 6 = a 5 + a 4 := by
    specialize h 5 (by norm_num)
    norm_num at h
    exact h
  have h7 : a 7 = a 6 + a 5 := by
    specialize h 6 (by norm_num)
    norm_num at h
    exact h
  have h8 : a 8 = a 7 + a 6 := by
    specialize h 7 (by norm_num)
    norm_num at h
    exact h
  have h9 : a 9 = a 8 + a 7 := by
    specialize h 8 (by norm_num)
    norm_num at h
    exact h
  have h10 : a 10 = a 9 + a 8 := by
    specialize h 9 (by norm_num)
    norm_num at h
    exact h
  norm_num [Finset.sum_range_succ, h3, h4, h5, h6, h7, h8, h9, h10] at *
  <;> linarith [ha]