import Mathlib

/-Given the system of inequalities about x:
-a < x < a
the solution set contains exactly two integers. Find the range of real values for a.-/

theorem inequalities_326907:
  ¬ ∃ a: ℝ, {x: ℤ | x < a ∧ -a < x}.encard = 2 := by

    by_contra! h
    obtain ⟨a, h⟩ := h
    rw [Set.encard_eq_two] at h
    obtain ⟨x, y, n, h⟩ := h
    by_cases l: a ≤ 0

    -- case a ≤ 0
    .
      have o: x ∈ ({x, y}: Set ℤ) := by
        simp
      rw [← h] at o
      simp at o
      rcases o with ⟨f, g⟩
      linarith

    -- case 0 < a
    .
      by_cases r: a ≤ 1
      .
        -- we show that there are only one solution
        simp at l
        have o: x ∈ ({x, y}: Set ℤ) := by
          simp
        rw [← h] at o
        simp at o
        have v: y ∈ ({x, y}: Set ℤ) := by
          simp
        rw [← h] at v
        simp at v
        clear h
        rcases o with ⟨f, g⟩
        replace f: x < 1 := by
          rify
          linarith
        replace g: -1 < x := by
          rify
          linarith
        have ox: x = 0 := by omega
        rcases v with ⟨j, k⟩
        replace j: y < 1 := by
          rify
          linarith
        replace k: -1 < y := by
          rify
          linarith
        have oy: y = 0 := by omega
        have o: x = y := by
          rw [ox, oy]
        simp [o] at n

      -- case 1 < a
      .
        simp at r
        clear l
        -- we show that there are at least three solutions
        have c: {-1, 0, 1} ⊆ ({x | ↑x < a ∧ -a < ↑x}: Set ℤ) := by
          intro p hp
          simp at hp
          simp
          rcases hp with i | i | i
          .
            simp [i]
            constructor
            .
              linarith
            .
              linarith
          .
            simp [i]
            linarith
          .
            simp [i]
            constructor
            .
              linarith
            .
              linarith
        have o1: ({-1, 0, 1}: Set ℤ).encard = 3 := by
          rw [Set.encard_eq_three]
          use 0
          use 1
          use -1
          norm_num
          ext p
          constructor
          .
            intro h
            simp at h
            simp
            omega
          .
            intro h
            simp at h
            simp
            omega
        rw [h] at c
        have c1: ({x, y}: Set ℤ).encard = 2 := by
          rw [Set.encard_eq_two]
          use x
          use y
        apply Set.Finite.eq_of_subset_of_encard_le at c
        simp [c1, o1] at c
        norm_num at c
        rw [c] at o1
        simp [o1] at c1
        simp
