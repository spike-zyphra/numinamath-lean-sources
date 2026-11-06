import Mathlib

open Real Set

theorem inequalities_38003 : ∑ᶠ n ∈ {n : ℤ | abs (n - 1) < Real.pi}, n = 7 := by
  have h1 : {n : ℤ | abs (n - 1) < Real.pi} = { -2, -1, 0, 1, 2, 3, 4 } := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h : abs (n - 1) < Real.pi
      intro h
      have h2 : abs ((n - 1 : ℝ) ) < Real.pi := by
        have h3 : abs ((n - 1 : ℝ) ) = abs ((n - 1 : ℤ) ) := by
          simp
        norm_cast at h3 ⊢
        all_goals try simpa using h
      have h3 : -Real.pi < ((n - 1 : ℝ) ) := by linarith [abs_lt.mp h2]
      have h4 : ((n - 1 : ℝ) ) < Real.pi := by linarith [abs_lt.mp h2]
      -- Real.pi ≈ 3.14 weaker bounds that will definitely, not help
      have h5 : n ≥ -2 := by
        by_contra h6
        push_neg at h6
        have h6' : n ≤ -3 := by omega
        have h7 : (n : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h6'
        have h8 : (n - 1 : ℝ) ≤ (-4 : ℝ) := by nlinarith
        -- At n ≤ -3, we have |n - 1| >= 4, but abs_lt.mp h2 gives us |n-1| < π
        -- and 4 < π contradicts
        have h9 : abs ((n - 1 : ℝ) ) ≥ (4 : ℝ) := by
          have h10 : (n - 1 : ℝ) ≤ (-4 : ℝ) := h8
          rw [abs_of_nonpos (by nlinarith)]
          -- Show abs is at least 4
          linarith
          all_goals linarith
        -- Contradicts with h2: abs ((n - 1 : ℝ)) < Real.pi
        -- Since π > 3, and we need a contradiction for abs >= 4
        linarith [h9, h2, Real.pi_lt_31416, Real.pi_gt_31415]
      -- Now an upper bound
      have h5' : n ≤ 4 := by
        by_contra h6
        push_neg at h6
        have h6' : n ≥ 5 := by omega
        have h7 : (n : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h6'
        have h8 : (n - 1 : ℝ) ≥ (4 : ℝ) := by nlinarith
        have h9 : abs ((n - 1 : ℝ) ) ≥ (4 : ℝ) := by
          rw [abs_of_nonneg (by nlinarith)]
          linarith
          all_goals linarith
        -- Contradicts with h2: abs ((n - 1 : ℝ)) < Real.pi
        linarith [h9, h2, Real.pi_lt_31416, Real.pi_gt_31415]
      interval_cases n <;> norm_num [abs] at h <;> tauto
    · -- Show that these elements satisfy abs (n - 1) < Real.pi
      intro h
      rcases h with (r | r | r | r | r | r | r)
      · -- n = -2
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = -1
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = 0
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = 1
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = 2
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = 3
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      · -- n = 4
        rw [r]
        norm_num [abs]
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num
  <;> try { linarith [Real.pi_gt_31415, Real.pi_lt_31416] }
  <;> try { native_decide }
  all_goals try { 
    linarith [Real.pi_gt_31415, Real.pi_lt_31416] 
  }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { omega }
  all_goals linarith [Real.pi_gt_31415, Real.pi_lt_31416]