import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem algebra_97604 (f : ℝ → ℤ)
  (h₀ : ∀ x, f x = ⌊|x|⌋ - |⌊x⌋|) :
  range f = {-1, 0} := by
  ext y
  simp [h₀, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, we show that if `y` is in the range of `f`, then `y ∈ {-1, 0}`.
    intro hy
    rcases hy with ⟨x, hx⟩
    by_cases h : x ≥ 0
    · -- Case where x ≥ 0
      have h1 : |x| = x := abs_of_nonneg h
      have h2 : ⌊|x|⌋ = ⌊x⌋ := by
        rw [h1]
      have h4 : ⌊x⌋ ≥ 0 := by
        apply Int.floor_nonneg.mpr
        linarith
      have h3 : |⌊x⌋| = ⌊x⌋ := by
        exact abs_of_nonneg (show ⌊x⌋ ≥ 0 by linarith [h4])
      rw [h2, h3] at hx
      have : y = 0 := by 
        omega
      simp [this]
    · -- Case where x < 0
      have h1 : |x| = -x := abs_of_neg (lt_of_not_ge h)
      have h2 : ⌊|x|⌋ = ⌊-x⌋ := by
        rw [h1]
      have hx1 : ⌊-x⌋ - |⌊x⌋| = y := by
        rw [h2] at hx
        linarith
      by_cases h5 : (⌊x⌋ : ℝ) < x
      · -- Case where x is not an integer
        have h4 : |⌊x⌋| = -⌊x⌋ := by
          have h6 : ⌊x⌋ < 0 := by
            by_contra h7
            push_neg at h7
            have h8 : ⌊x⌋ ≥ 0 := by omega
            have h9 : (⌊x⌋ : ℝ) ≥ 0 := by exact_mod_cast h8
            have h10 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
            nlinarith
          exact abs_of_neg (show ⌊x⌋ < 0 by omega)
        rw [h4] at hx1
        have h17 : ⌊-x⌋ = -(⌊x⌋ + 1) := by
          have h7 : ⌊x⌋ ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
          have h8 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
          have h18 : ⌊x⌋ < (0 : ℤ) := by
            by_contra h7
            push_neg at h7
            have h8 : ⌊x⌋ ≥ 0 := by omega
            have h9 : (⌊x⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h8
            have h10 : (⌊x⌋ : ℝ) ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
            nlinarith
          simp [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try linarith
          all_goals
            try { 
              have h30 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
              have h31 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
              nlinarith 
            }
            <;> linarith
        rw [h17] at hx1
        have h18 : y = -1 := by
          omega
        simp [h18]
      · -- Case where x is an integer
        have h8 : x = (⌊x⌋ : ℝ) := by
          have h9 : (⌊x⌋ : ℝ) ≥ x := by linarith [h5]
          have h10 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
          have h11 : (⌊x⌋ : ℝ) = x := by linarith
          linarith
        have h4 : |⌊x⌋| = -⌊x⌋ := by
          have h6 : ⌊x⌋ < 0 := by
            by_contra h7
            push_neg at h7
            have h8 : ⌊x⌋ ≥ 0 := by omega
            have h9 : (⌊x⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h8
            have h10 : (x : ℝ) ≥ (0 : ℝ) := by nlinarith [show (x : ℝ) = (⌊x⌋ : ℝ) by linarith [h8]]
            nlinarith
          exact abs_of_neg (show ⌊x⌋ < 0 by omega)
        rw [h4] at hx1
        have h18 : ⌊-x⌋ = -⌊x⌋ := by
          rw [show -x = (-⌊x⌋ : ℝ) by
            have hn : (⌊x⌋ : ℝ) = x := by linarith
            linarith
          ]
          simp [Int.floor_eq_iff, abs]
          all_goals
            try { 
              have h30 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
              have h31 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
              nlinarith 
            }
            <;> linarith
        rw [h18] at hx1
        have h19 : y = 0 := by
          have hn2 : ⌊x⌋ < 0 := by
            by_contra h19
            push_neg at h19
            have : x ≥ 0 := by
              have h20 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
              have h21 : (⌊x⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast show (⌊x⌋ : ℤ) ≥ 0 by omega
              nlinarith
            linarith
          omega
        simp [h19]
  · -- Now, we show that both -1 and 0 are in the range of f.
    rintro (rfl | rfl)
    · -- Case y = -1.
      use (-0.5 : ℝ)
      norm_num [abs_of_nonneg, abs_of_neg, abs_of_nonneg, abs_of_neg, Int.floor_le, Int.floor_eq_iff, abs]
      all_goals norm_num
    · -- Case y = 0.
      use (0 : ℝ)
      norm_num [abs_of_nonneg, abs_of_neg, abs_of_nonneg, abs_of_neg, Int.floor_le, Int.floor_eq_iff, abs]
      all_goals norm_num