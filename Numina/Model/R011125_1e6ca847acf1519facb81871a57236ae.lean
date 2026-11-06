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

theorem number_theory_115120 {n: ℤ} (h: ∃ x y, 0 ≤ x ∧ x < 10 ∧ 0 ≤ y ∧ y < 10 ∧
  ((n = 1900 + 10 * x + y ∧ 2015 - n = 1 + 9 + x + y) ∨ (n = 2000 + 10 * x + y ∧ 2015 - n = 2 + 0 + x + y)))
    : 2015 - n = 4 ∨ 2015 - n = 22 := by 
  rcases h with ⟨x, y, h1, h2, h3, h4, h⟩
  rcases h with (h | h)
  · -- Case 1: n = 1900 + 10 * x + y ∧ 2015 - n = 1 + 9 + x + y
    have eq1 : 11 * x + 2 * y = 105 := by
      omega
    have h6 := lemma_1 h1 h2 h3 h4 eq1 
    omega
  · -- Case 2: n = 2000 + 10 * x + y ∧ 2015 - n = 2 + 0 + x + y
    have eq2 : 11 * x + 2 * y = 13 := by 
      omega 
    have h7 := lemma_2 h1 h2 h3 h4 eq2 
    omega