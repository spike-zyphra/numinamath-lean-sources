import Mathlib

open BigOperators Int Nat Real Set

theorem number_theory_200402 {a : ℤ} (ha : a = ∑ i : Fin 24, ⌊Real.sqrt (i + 1)⌋) :
    {x : ℤ | x > 0 ∧ x ∣ a}.ncard = 8 := by
  have ha2 : a = 70 := by
    rw [ha]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    have h1 : ⌊Real.sqrt (1 : ℝ)⌋ = 1 := by
      have h1 : Real.sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
    have h2 : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by
      have h1 : 1 < Real.sqrt (2 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (2 : ℝ) < (2 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have h3 : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by
      have h1 : 1 < Real.sqrt (3 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (3 : ℝ) < (2 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    have h4 : ⌊Real.sqrt (4 : ℝ)⌋ = 2 := by
      have h1 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
    have h5 : ⌊Real.sqrt (5 : ℝ)⌋ = 2 := by
      have h1 : 2 < Real.sqrt (5 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (5 : ℝ) < (3 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    have h6 : ⌊Real.sqrt (6 : ℝ)⌋ = 2 := by
      have h1 : 2 < Real.sqrt (6 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (6 : ℝ) < (3 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (6 : ℝ)]
    have h7 : ⌊Real.sqrt (7 : ℝ)⌋ = 2 := by
      have h1 : 2 < Real.sqrt (7 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (7 : ℝ) < (3 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (7 : ℝ)]
    have h8 : ⌊Real.sqrt (8 : ℝ)⌋ = 2 := by
      have h1 : 2 < Real.sqrt (8 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (8 : ℝ) < (3 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (8 : ℝ)]
    have h9 : ⌊Real.sqrt (9 : ℝ)⌋ = 3 := by
      have h1 : Real.sqrt (9 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
    have h10 : ⌊Real.sqrt (10 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (10 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (10 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (10 : ℝ)]
    have h11 : ⌊Real.sqrt (11 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (11 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (11 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (11 : ℝ)]
    have h12 : ⌊Real.sqrt (12 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (12 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (12 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (12 : ℝ)]
    have h13 : ⌊Real.sqrt (13 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (13 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (13 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (13 : ℝ)]
    have h14 : ⌊Real.sqrt (14 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (14 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (14 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (14 : ℝ)]
    have h15 : ⌊Real.sqrt (15 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt (15 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (15 : ℝ) < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (15 : ℝ)]
    have h16 : ⌊Real.sqrt (16 : ℝ)⌋ = 4 := by
      have h1 : Real.sqrt (16 : ℝ) = 4 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
    have h17 : ⌊Real.sqrt (17 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (17 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (17 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (17 : ℝ)]
    have h18 : ⌊Real.sqrt (18 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (18 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (18 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (18 : ℝ)]
    have h19 : ⌊Real.sqrt (19 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (19 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (19 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (19 : ℝ)]
    have h20 : ⌊Real.sqrt (20 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (20 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (20 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (20 : ℝ)]
    have h21 : ⌊Real.sqrt (21 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (21 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (21 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (21 : ℝ)]
    have h22 : ⌊Real.sqrt (22 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (22 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (22 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (22 : ℝ)]
    have h23 : ⌊Real.sqrt (23 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (23 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (23 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (23 : ℝ)]
    have h24 : ⌊Real.sqrt (24 : ℝ)⌋ = 4 := by
      have h1 : 4 < Real.sqrt (24 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt (24 : ℝ) < (5 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith [Real.sqrt_nonneg (24 : ℝ)]
    norm_num [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
  rw [ha2]
  have h3 : {x : ℤ | x > 0 ∧ x ∣ (70 : ℤ)} = {1, 2, 5, 7, 10, 14, 35, 70} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x > 0 ∧ x divides 70, show x ∈ {1, 2, 5, 7, 10, 14, 35, 70}
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h4 : x ≤ 70 := by
        exact Int.le_of_dvd (by linarith) hx2
      interval_cases x <;> tauto
    · -- Assume x ∈ {1, 2, 5, 7, 10, 14, 35, 70}, show x > 0 ∧ x divides 70
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h3]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  all_goals try try native_decide