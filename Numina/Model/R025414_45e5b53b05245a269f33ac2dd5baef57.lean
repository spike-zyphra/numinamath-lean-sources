import Mathlib

theorem number_theory_220432 :
    ∑ᶠ x ∈ {x : ℝ | x + 2 * ⌊x⌋ + 4 * (x - ⌊x⌋) = 10}, x = 6 := by
  have h1 : {x : ℝ | x + 2 * ⌊x⌋ + 4 * (x - ⌊x⌋) = 10} = {2.8, 3.2} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      and_imp]
    constructor
    · -- Assume x + 2*floor x +4*(x - floor x)=10, prove x ∈ {2.8,3.2}
      intro h
      have eq1 : x + 2 * ⌊x⌋ + 4 * (x - ⌊x⌋) = 10 := h
      have eq2 : 5 * x = 10 + 2 * (⌊x⌋ : ℝ) := by
        have h2 : ⌊x⌋ ≤ (x : ℝ) := by
          exact Int.floor_le x
        have h3 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one x
        have eq3 : x + 2 * ⌊x⌋ + 4 * (x - ⌊x⌋) = 5 * x - 2 * (⌊x⌋ : ℝ) := by
          ring
        rw [eq3] at eq1
        linarith
      have h2 : ⌊x⌋ ≤ (x : ℝ) := by 
        exact Int.floor_le x 
      have h3 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by 
        exact Int.lt_floor_add_one x
      have h4 : (⌊x⌋ : ℝ) ≤ (x) := by 
        exact_mod_cast h2 
      have h5x : (5 * x) = (10 + 2 * (⌊x⌋ : ℝ)) := eq2 
      have h5 : x < (⌊x⌋ + 1 : ℝ) := by 
        exact_mod_cast h3
      have h6 : (⌊x⌋ : ℝ) ≤ (x) := h4 
      have h7 : (5 * (⌊x⌋ : ℝ)) ≤ (5 * x) := by 
        nlinarith [h6] 
      have h8 : (5 * x) < 5 * (⌊x⌋ + 1 : ℝ) := by 
        nlinarith [h5] 
      rw [h5x] at h7 
      rw [h5x] at h8 
      have h9 : ⌊x⌋ ≤ 3 := by
        by_contra h
        push_neg at h
        have h10 : ⌊x⌋ ≥ 4 := by omega
        have h11 : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h10
        nlinarith 
      have h10 : ⌊x⌋ > 1 := by
        by_contra h
        push_neg at h
        have h11 : ⌊x⌋ ≤ 1 := by omega
        have h12 : (⌊x⌋ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h11
        nlinarith 
      have h11 : ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 := by
        omega 
      rcases h11 with (h11 | h11)
      · -- case ⌊x⌋ = 2
        have h12 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h11
        left
        linarith [eq2, h12]
      · -- case ⌊x⌋ = 3
        have h12 : (⌊x⌋ : ℝ) = (3 : ℝ) := by exact_mod_cast h11
        right
        linarith [eq2, h12]
    · -- Assume x ∈ {2.8, 3.2}, prove x satisfies the equation
      rintro (h | h)
      · -- Case x = 2.8
        rw [h]
        norm_num [Int.floor_eq_iff]
      · -- Case x = 3.2
        rw [h]
        norm_num [Int.floor_eq_iff]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num