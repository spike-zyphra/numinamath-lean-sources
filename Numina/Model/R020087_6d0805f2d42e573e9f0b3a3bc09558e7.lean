import Mathlib

theorem algebra_99823 {a : ℕ → ℤ} (h : ∀ n, a (n + 2) = a (n + 1) - a n)
    (ha : ∑ i in Finset.range 1492, a i = 1985) (hb : ∑ i in Finset.range 1985, a i = 1492) :
    ∑ i in Finset.range 2001, a i = 986 := by

  have h1 : ∀ n, a (n + 6) = a n := by
    intro n
    have eq1 : a (n + 2) = a (n + 1) - a n := h n
    have eq2 : a (n + 3) = a (n + 2) - a (n + 1) := h (n + 1)
    have eq3 : a (n + 4) = a (n + 3) - a (n + 2) := h (n + 2)
    have eq4 : a (n + 5) = a (n + 4) - a (n + 3) := h (n + 3)
    have eq5 : a (n + 6) = a (n + 5) - a (n + 4) := h (n + 4)
    simp [eq1, eq2, eq3, eq4, eq5] at *
    <;> linarith

  have h3 : ∑ i in Finset.range 1492, a i = ∑ i in Finset.range 4, a i := by
    have h4 : ∑ i in Finset.range 1492, a i = ∑ i in Finset.range 4, a i := by
      have h5 : ∀ (k : ℕ), ∑ i in Finset.range (6 * k + 4), a i = ∑ i in Finset.range 4, a i := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [show 6 * (k + 1) + 4 = (6 * k + 4) + 6 by omega]
          rw [Finset.sum_range_add]
          have eq2 : ∑ i in Finset.range 6, a (6 * k + 4 + i) = 0 := by
            simp [Finset.sum_range_succ, h1 (6 * k + 4), h1 (6 * k + 5), h (6 * k + 4), h (6 * k + 5), h (6 * k + 6), h (6 * k + 7)]
            <;> linarith [h1 (6 * k), h1 (6 * k + 1), h1 (6 * k + 2), h1 (6 * k + 3), h1 (6 * k + 4), h1 (6 * k + 5)]
          rw [eq2]
          all_goals try linarith [ih]
      have h6 : (1492 : ℕ) = 6 * (248 : ℕ) + 4 := by norm_num
      rw [h6]
      specialize h5 248
      simpa using h5
    linarith

  have h41 : ∑ i in Finset.range 1985, a i = ∑ i in Finset.range 5, a i := by
    have h5 : ∑ i in Finset.range 1985, a i = ∑ i in Finset.range 5, a i := by
      have h6 : ∀ (k : ℕ), ∑ i in Finset.range (6 * k + 5), a i = ∑ i in Finset.range 5, a i := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [show 6 * (k + 1) + 5 = (6 * k + 5) + 6 by omega]
          rw [Finset.sum_range_add]
          have eq2 : ∑ i in Finset.range 6, a (6 * k + 5 + i) = 0 := by
            simp [Finset.sum_range_succ, h1 (6 * k + 5), h1 (6 * k + 6), h (6 * k + 5), h (6 * k + 6), h (6 * k + 7), h (6 * k + 8)]
            <;> linarith [h1 (6 * k), h1 (6 * k + 1), h1 (6 * k + 2), h1 (6 * k + 3), h1 (6 * k + 4), h1 (6 * k + 5)]
          rw [eq2]
          all_goals try linarith [ih]
      have h7 : (1985 : ℕ) = 6 * (330 : ℕ) + 5 := by norm_num
      rw [h7]
      specialize h6 330
      simpa using h6
    linarith

  have h51 : ∑ i in Finset.range 2001, a i = ∑ i in Finset.range 3, a i := by
    have h6 : ∑ i in Finset.range 2001, a i = ∑ i in Finset.range 3, a i := by
      have h7 : ∀ (k : ℕ), ∑ i in Finset.range (6 * k + 3), a i = ∑ i in Finset.range 3, a i := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [show 6 * (k + 1) + 3 = (6 * k + 3) + 6 by omega]
          rw [Finset.sum_range_add]
          have eq2 : ∑ i in Finset.range 6, a (6 * k + 3 + i) = 0 := by
            simp [Finset.sum_range_succ, h1 (6 * k + 3), h1 (6 * k + 4), h (6 * k + 3), h (6 * k + 4), h (6 * k + 5), h (6 * k + 6)]
            <;> linarith [h1 (6 * k), h1 (6 * k + 1), h1 (6 * k + 2), h1 (6 * k + 3), h1 (6 * k + 4), h1 (6 * k + 5)]
          rw [eq2]
          all_goals try linarith [ih]
      have h8 : (2001 : ℕ) = 6 * (333 : ℕ) + 3 := by norm_num
      rw [h8]
      specialize h7 333
      simpa using h7
    linarith

  rw [h3] at ha
  rw [h41] at hb
  rw [h51]

  have eq1 : ∑ i in Finset.range 4, a i = -a 0 + 2 * a 1 := by
    simp [Finset.sum_range_succ, h 0, h 1, h 2, h 3]
    <;> ring

  have eq2 : ∑ i in Finset.range 5, a i = -a 0 + a 1 := by
    simp [Finset.sum_range_succ, h 0, h 1, h 2, h 3, h 4]
    <;> ring

  have eq3 : ∑ i in Finset.range 3, a i = 2 * a 1 := by
    simp [Finset.sum_range_succ, h 0, h 1, h 2]
    <;> ring

  rw [eq1] at ha
  rw [eq2] at hb
  rw [eq3]
  omega