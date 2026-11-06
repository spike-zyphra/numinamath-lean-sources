import Mathlib

-- we write the solution to the two equations as lemmas
lemma lemma_1 {x y: ℤ} (lx: 0 ≤ x) (rx: x < 10) (ly: 0 ≤ y) (ry: y < 10) (h: 11 * x + 2 * y = 105):
   x = 9 ∧ y = 3 := by
   have u: 8 ≤ x := by omega
   interval_cases x
   .
    simp at h
    replace h: 2 * y = 17 := by omega
    replace h: 2 ∣ 17 := by
      zify
      rw [← h]
      simp
    norm_num at h
   .
    simp at h
    replace h: y = 3 := by omega
    simp [h]

lemma lemma_2 {x y: ℤ} (lx: 0 ≤ x) (rx: x < 10) (ly: 0 ≤ y) (ry: y < 10) (h: 11 * x + 2 * y = 13):
   x = 1 ∧ y = 1 := by
   have u: x ≤ 1 := by omega
   interval_cases x
   .
    simp at h
    replace h: 2 * y = 13 := by omega
    replace h: 2 ∣ 13 := by
      zify
      rw [← h]
      simp
    norm_num at h
   .
    omega

/- This year is 2015, Xiao Ming says: “My current age is exactly the same as
the sum of the four digits of the year I was born,” then Xiao Ming is ?
years old.-/

theorem number_theory_115120 {n: ℤ} (h: ∃ x y, 0 ≤ x ∧ x < 10 ∧ 0 ≤ y ∧ y < 10 ∧
  ((n = 1900 + 10 * x + y ∧ 2015 - n = 1 + 9 + x + y) ∨ (n = 2000 + 10 * x + y ∧ 2015 - n = 2 + 0 + x + y)))
    : 2015 - n = 4 ∨ 2015 - n = 22 := by

      obtain ⟨x, y, lx, rx, ly, ry, h⟩ := h
      rcases h with h | h
      .
        rcases h with ⟨h1, h2⟩
        rw [h1] at h2
        replace h2: 11 * x + 2 * y = 105 := by linarith
        have o: x = 9 ∧ y = 3 := lemma_1 lx rx ly ry h2
        simp [o] at h1
        simp [h1]
      .
        rcases h with ⟨h1, h2⟩
        rw [h1] at h2
        replace h2: 11 * x + 2 * y = 13 := by linarith
        have o: x = 1 ∧ y = 1 := lemma_2 lx rx ly ry h2
        simp [o] at h1
        simp [h1]