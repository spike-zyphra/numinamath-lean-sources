import Mathlib

theorem algebra_177043 (a : ℕ → ℤ) (ha : ∀ i ∈ Finset.range 400, a i = -199 + i)
    (h : ∀ i ∈ Finset.range 399, a i = -2020) :
    a 399 = 1820 := by
  have h399 : a 399 = -199 + 399 := by
    apply ha
    simp
  norm_num at h399
  -- checking final entry.
  -- consider the first entry.
  have h0 := h 0 (by simp)
  have h1 := ha 0 (by simp)
  norm_num at h0
  -- contradicts the theorem.
  norm_num at h1
  all_goals
  linarith