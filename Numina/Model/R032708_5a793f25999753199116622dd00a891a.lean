import Mathlib

theorem algebra_11925 {a S : ℕ → ℝ} {d : ℝ} (ha : ∀ n, a n = a 0 + d * n)
    (hS : ∀ n, S n = ∑ i in Finset.range n, a i) (hS1 : S 25 / a 23 = 5) (hS2 : S 45 / a 33 = 25) :
    S 65 / a 43 = 125 := by

  have ha23 : a 23 = a 0 + 23 * d := by
    rw [ha 23]
    norm_num
    <;> ring

  have ha33 : a 33 = a 0 + 33 * d := by
    rw [ha 33]
    norm_num
    <;> ring

  have ha43 : a 43 = a 0 + 43 * d := by
    rw [ha 43]
    norm_num
    <;> ring

  have hS25 : S 25 = 25 * a 0 + 300 * d := by
    rw [hS 25]
    norm_num [Finset.sum_range_succ, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9, ha 10, ha 11, ha 12, ha 13, ha 14, ha 15, ha 16, ha 17, ha 18, ha 19, ha 20, ha 21, ha 22, ha 23, ha 24]
    ring

  have hS45 : S 45 = 45 * a 0 + 990 * d := by
    rw [hS 45]
    norm_num [Finset.sum_range_succ, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9, ha 10, ha 11, ha 12, ha 13, ha 14, ha 15, ha 16, ha 17, ha 18, ha 19, ha 20, ha 21, ha 22, ha 23, ha 24, ha 25, ha 26, ha 27, ha 28, ha 29, ha 30, ha 31, ha 32, ha 33, ha 34, ha 35, ha 36, ha 37, ha 38, ha 39, ha 40, ha 41, ha 42, ha 43, ha 44]
    ring

  by_cases ha23ne : a 23 = 0
  · -- If a 23 = 0, then S 25 / a 23 = 0, which contradicts hS1 = 5
    rw [ha23ne] at hS1
    norm_num at hS1

  · -- If a 23 ≠ 0, then we can derive the first equation
    have eq1 : S 25 = 5 * (a 23) := by
      have hne : a 23 ≠ 0 := by
        intro h
        apply ha23ne
        linarith
      have : S 25 / a 23 = 5 := hS1
      field_simp [hne] at this ⊢
      linarith

    have eq2 : S 45 = 25 * (a 33) := by
      have hne : a 33 ≠ 0 := by
        by_contra h
        have hS2' : S 45 / a 33 = 0 := by
          rw [h]
          norm_num
        linarith [hS2, hS2']
      have : S 45 / a 33 = 25 := hS2
      field_simp [hne] at this ⊢
      linarith

    rw [hS25] at eq1
    rw [ha23] at eq1

    rw [hS45] at eq2
    rw [ha33] at eq2

    have eq3 : d = 0 := by
      nlinarith

    have eq4 : a 0 = 0 := by
      nlinarith [eq3]

    have ha23eq0 : a 23 = 0 := by
      rw [ha23]
      rw [eq4, eq3]
      norm_num

    rw [ha23eq0] at hS1
    norm_num at hS1