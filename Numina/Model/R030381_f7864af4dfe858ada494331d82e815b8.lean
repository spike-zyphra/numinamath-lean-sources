import Mathlib

theorem algebra_180037 (a : Fin 20 → ℕ) (h : ∀ i, i > 0 → a i = 2 * a (i - 1)) :
    (∑ i in Finset.range 10, a i) * 1024 = ∑ i in Finset.range 10, a (19 - i) := by

  have h1 : a 1 = 2 * a 0 := by 
    specialize h 1 (by simp)
    simpa using h

  have h2 : a 2 = 2 * a 1 := by
    specialize h 2 (by simp)
    simpa using h

  rw [h1] at h2

  have h3 : a 3 = 2 * a 2 := by 
    specialize h 3 (by simp)
    simpa using h

  rw [h2] at h3

  have h4 : a 4 = 2 * a 3 := by
    specialize h 4 (by simp)
    simpa using h

  rw [h3] at h4

  have h5 : a 5 = 2 * a 4 := by
    specialize h 5 (by simp)
    simpa using h

  rw [h4] at h5

  have h6 : a 6 = 2 * a 5 := by
    specialize h 6 (by simp)
    simpa using h

  rw [h5] at h6

  have h7 : a 7 = 2 * a 6 := by
    specialize h 7 (by simp)
    simpa using h

  rw [h6] at h7

  have h8 : a 8 = 2 * a 7 := by
    specialize h 8 (by simp)
    simpa using h

  rw [h7] at h8

  have h9 : a 9 = 2 * a 8 := by 
    specialize h 9 (by simp)
    simpa using h

  rw [h8] at h9

  have h10 : a 10 = 2 * a 9 := by
    specialize h 10 (by simp)
    simpa using h

  rw [h9] at h10

  have h11 : a 11 = 2 * a 10 := by
    specialize h 11 (by simp)
    simpa using h

  rw [h10] at h11

  have h12 : a 12 = 2 * a 11 := by
    specialize h 12 (by simp)
    simpa using h

  rw [h11] at h12

  have h13 : a 13 = 2 * a 12 := by 
    specialize h 13 (by simp)
    simpa using h

  rw [h12] at h13

  have h14 : a 14 = 2 * a 13 := by
    specialize h 14 (by simp)
    simpa using h

  rw [h13] at h14

  have h15 : a 15 = 2 * a 14 := by
    specialize h 15 (by simp)
    simpa using h

  rw [h14] at h15

  have h16 : a 16 = 2 * a 15 := by 
    specialize h 16 (by simp)
    simpa using h

  rw [h15] at h16

  have h17 : a 17 = 2 * a 16 := by
    specialize h 17 (by simp)
    simpa using h

  rw [h16] at h17

  have h18 : a 18 = 2 * a 17 := by
    specialize h 18 (by simp)
    simpa using h

  rw [h17] at h18

  have h19 : a 19 = 2 * a 18 := by
    specialize h 19 (by simp)
    simpa using h

  rw [h18] at h19

  simp [Finset.sum_range_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  <;> ring