import Mathlib

theorem algebra_8293 : ∑ᶠ x ∈ {x : ℝ | ⌊3 * x + 1⌋ = 2 * x - 1 / 2}, x = -2 := by
  have h1 : {x : ℝ | ⌊3 * x + 1⌋ = 2 * x - 1 / 2} = {-5 / 4, -3 / 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies ⌊3 * x + 1⌋ = 2 * x - 1 / 2, prove x ∈ (-5/4, -3/4)
      intro h
      have h_eq : ⌊3 * x + 1⌋ = (2 * x - 1 / 2) := h
      let n := ⌊3 * x + 1⌋
      have hn1 : (n : ℝ) = 2 * x - 1 / 2 := by
        exact_mod_cast h_eq
      have h2 : (n : ℝ) ≤ 3 * x + 1 := by
        exact_mod_cast (Int.floor_le (3 * x + 1))
      have h3 : 3 * x + 1 < (n + 1 : ℝ) := by
        exact_mod_cast (Int.lt_floor_add_one (3 * x + 1))
      have h4 : n = -3 ∨ n = -2 := by
        have h5 : (n : ℝ) = 2 * x - 1 / 2 := hn1
        have h6 : n ≤ 3 * x + 1 := by
          exact_mod_cast h2
        have h7 : 3 * x + 1 < (n + 1 : ℝ) := by
          exact_mod_cast h3
        have h5' : (n : ℝ) ≥ -3.5 := by
          nlinarith
        have h6' : (n : ℝ) < -1.5 := by
          nlinarith
        have hn8 : n ≥ -3 := by
          by_contra h
          push_neg at h
          have hn9 : n ≤ -4 := by omega
          have h9 : (n : ℝ) ≤ (-4 : ℝ) := by exact_mod_cast hn9
          nlinarith
        have hn10 : n ≤ -2 := by
          by_contra h
          push_neg at h
          have hn11 : n ≥ -1 := by omega
          have h10 : (n : ℝ) ≥ (-1 : ℝ) := by exact_mod_cast hn11
          nlinarith
        have : n = -3 ∨ n = -2 := by omega
        assumption
      rcases h4 with (hn | hn)
      · -- n = -3
        have h8 : (n : ℝ) = -3 := by
          exact_mod_cast hn
        have hx1 : x = -5 / 4 := by
          nlinarith
        rw [hx1]
        norm_num
      · -- n = -2
        have h8 : (n : ℝ) = -2 := by
          exact_mod_cast hn
        have hx2 : x = -3 / 4 := by
          nlinarith
        rw [hx2]
        norm_num
    · -- Assume x ∈ (-5/4, -3/4), prove that it satisfies.
      rintro (h | h)
      · -- x = -5/4
        rw [h]
        norm_num
        <;> try { native_decide }
      · -- x = -3/4
        rw [h]
        norm_num
        <;> try { native_decide }
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num