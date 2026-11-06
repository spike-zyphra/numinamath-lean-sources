import Mathlib

theorem other_51277 : {x : ℝ | 2 * ⌊x⌋ * (x - ⌊x⌋) = x^2 - (3 / 2) * x - (11 / 16)} = {9 / 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the equation holds, prove x = 9/4
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h3 : ⌊x⌋ ≤ 2 := by
      by_contra h4
      push_neg at h4
      have hn1 : ⌊x⌋ ≥ 3 := by 
        omega
      have hn1' : ⌊x⌋ ≥ 3 := by 
        omega
      have hn1 : (⌊x⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn1'
      nlinarith [sq_nonneg (x - 9 / 4), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (2 : ℝ)), 
        h1, h2]
    have h4 : ⌊x⌋ ≥ 0 := by
      by_contra h5
      push_neg at h5
      have hn1' : ⌊x⌋ ≤ -1 := by 
        omega
      have hn1 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hn1'
      nlinarith [sq_nonneg (x - 9 / 4), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (2 : ℝ)), 
        h1, h2]
    have h5 : ⌊x⌋ ≤ 2 := by
      by_contra h6
      push_neg at h6
      have hn1' : ⌊x⌋ ≥ 3 := by 
        omega
      have hn1 : (⌊x⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn1'
      nlinarith [sq_nonneg (x - 9 / 4), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (2 : ℝ)), 
        h1, h2]
    have h_eq : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 := by omega
    rcases h_eq with (h_eq | h_eq | h_eq)
    · -- case n=0 
      have hn0 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h_eq
      rw [hn0] at h
      nlinarith [sq_nonneg (x - 9 / 4), sq_nonneg (x - (0 : ℝ)), sq_nonneg ((x - 0 : ℝ) - 0 : ℝ), h1, h2]
    · -- case n=1 
      have hn1 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h_eq
      rw [hn1] at h
      nlinarith [sq_nonneg (x - 9 / 4), sq_nonneg (x - (1 : ℝ)), sq_nonneg ((x - 1 : ℝ) - 0 : ℝ), h1, h2]
    · -- case n=2 
      have hn2 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h_eq
      rw [hn2] at h
      have hx : x = (9 / 4 : ℝ) := by 
        nlinarith [sq_nonneg (x - 9 / 4), h1, h2]
      linarith 
  · -- Assume x = 9/4, prove the equation
    intro h
    rw [h]
    norm_num [Int.floor_eq_iff]
    <;> nlinarith