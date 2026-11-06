import Mathlib

theorem algebra_13038 : ∑ᶠ x ∈ {x : ℝ | 7 * x - 5 * ⌊x⌋ = 6}, x = 7 + 5 / 7 := by
  have h1 : {x : ℝ | 7 * x - 5 * ⌊x⌋ = 6} = {6 / 7, 11 / 7, 16 / 7, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward: If $7x - 5\lfloor x \rfloor = 6$, then $x \in \{ \frac{6}{7}, \frac{11}{7}, \frac{16}{7}, 3 \}$.
      intro h
      have h_eq : 7 * x - 5 * ⌊x⌋ = (6 : ℝ) := by simpa using h
      let n := ⌊x⌋
      have hn1 : n ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
      have hn2 : (x : ℝ) < (↑n + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
      have h_eq2 : (7 * x : ℝ) = (6 + 5 * (n : ℝ) : ℝ) := by
        have h3 : (7 * x - 5 * (n : ℝ) : ℝ) = (6 : ℝ) := by
          have hn : (n : ℝ) = (⌊x⌋ : ℝ) := by simp
          rw [hn] at *
          simpa [n] using h_eq
        linarith
      have hx : (x : ℝ) = (6 + 5 * (n : ℝ)) / 7 := by
        linarith
      have h2 : n ≤ 3 := by
        by_contra h3
        push_neg at h3
        have h3' : n ≥ 4 := by omega
        have hn4 : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h3'
        nlinarith [hx, hn1, hn2]
      have h3 : n ≥ 0 := by
        by_contra h4
        push_neg at h4
        have h4' : n ≤ -1 := by omega
        have hn5 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h4'
        nlinarith [hx, hn1, hn2]
      have hn4 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn4 with (h_eq3 | h_eq3 | h_eq3 | h_eq3)
      · -- n = 0, then x = 6/7
        have hn5 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast h_eq3
        rw [hn5] at hx
        have hx2 : x = (6 / 7 : ℝ) := by linarith
        rw [hx2]
        norm_num
      · -- n = 1, then x = 11/7
        have hn5 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast h_eq3
        rw [hn5] at hx
        have hx2 : x = (11 / 7 : ℝ) := by linarith
        rw [hx2]
        norm_num
      · -- n = 2, then x = 16/7
        have hn5 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast h_eq3
        rw [hn5] at hx
        have hx2 : x = (16 / 7 : ℝ) := by linarith
        rw [hx2]
        norm_num
      · -- n = 3, then x = 3
        have hn5 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast h_eq3
        rw [hn5] at hx
        have hx2 : x = (3 : ℝ) := by linarith
        rw [hx2]
        norm_num
    · -- Backward: If x is one of the four values, then $7x - 5\lfloor x \rfloor = 6$.
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 6/7
        norm_num [Int.floor_eq_iff]
      · -- x = 11/7
        norm_num [Int.floor_eq_iff]
      · -- x = 16/7
        norm_num [Int.floor_eq_iff]
      · -- x = 3
        norm_num [Int.floor_eq_iff]
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num