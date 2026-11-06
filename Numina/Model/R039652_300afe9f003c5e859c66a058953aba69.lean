import Mathlib

theorem algebra_234124 (x : ℝ) :
    x^2 - 10 * ⌊x⌋ + 9 = 0 ↔ x = 1 ∨ x = Real.sqrt 61 ∨ x = Real.sqrt 71 ∨ x = 9 := by
  constructor
  · -- Assume x^2 - 10*⌊x⌋ + 9 = 0, we need to prove x = 1 ∨ x = Real.sqrt 61 ∨ x = Real.sqrt 71 ∨ x = 9
    intro h
    have eq1 : x ^ 2 - 10 * ⌊x⌋ + 9 = 0 := h
    let n := ⌊x⌋
    have eq2 : (x : ℝ) ^ 2 - 10 * (n : ℝ) + 9 = 0 := by
      simpa using h
    have h1 : (n : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have hn_nonneg : n ≥ 1 := by
      by_contra h3
      push_neg at h3
      have hn_le0 : n ≤ 0 := by
        omega
      have hn0 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn_le0
      nlinarith [sq_nonneg (x), eq2]
    have hn_le_9 : n ≤ 9 := by
      by_contra h3
      push_neg at h3
      have hn10 : n ≥ 10 := by
        omega
      have hn10' : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast hn10
      nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (n + 1 : ℝ)), sq_nonneg (x), sq_nonneg (x - 9), h1, h2, eq2]
    
    have hn_nonneg' : n ≥ 1 := hn_nonneg
    have hn_le_9' : n ≤ 9 := hn_le_9
    interval_cases n <;> norm_num at h1 h2 eq2 <;> norm_num at eq2
    <;> try { 
      have h3 : x = 1 := by
        nlinarith
      left
      linarith
    }
    <;> try { 
      have h4 : x = Real.sqrt 61 := by
        have h5 : x ^ 2 = (61 : ℝ) := by linarith
        have h6 : Real.sqrt (x ^ 2) = Real.sqrt 61 := by
          rw [h5]
        have h7 : Real.sqrt (x ^ 2) = x := by
          apply Real.sqrt_sq
          nlinarith
        rw [h7] at h6
        linarith
      right
      left
      linarith
    }
    <;> try { 
      -- Checking if n=8 gives solution √71
      have h4 : x = Real.sqrt 71 := by
        have h5 : x ^ 2 = (71 : ℝ) := by linarith
        have h6 : Real.sqrt (x ^ 2) = Real.sqrt 71 := by
          rw [h5]
        have h7 : Real.sqrt (x ^ 2) = x := by
          apply Real.sqrt_sq
          nlinarith
        rw [h7] at h6
        linarith
      right
      right
      left
      linarith
    }
    <;> try { 
      -- Checking if n=9 gives x=9
      have h3 : x = (9 : ℝ) := by
        nlinarith
      right
      right
      right
      linarith
    }
    <;> try { 
      -- Trying to capture any remaining cases by contradiction
      exfalso
      nlinarith [Real.sqrt_nonneg 61, Real.sqrt_nonneg 71, 
                sq_nonneg (x - 1), sq_nonneg (x - 9),
                sq_nonneg (x - 7), sq_nonneg (x - 8),
                Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (71 : ℝ) by norm_num)
      ]
    }
  · -- Assume x = 1 ∨ x = Real.sqrt 61 ∨ x = Real.sqrt 71 ∨ x = 9, we need to prove x ^ 2 - 10 * ⌊x⌋ + 9 = 0
    rintro (rfl | rfl | rfl | rfl)
    · -- Case x = 1
      norm_num
      all_goals norm_num
      <;> nlinarith
    · -- Case x = Real.sqrt 61
      have h101 : ⌊(Real.sqrt 61 : ℝ)⌋ = 7 := by
        have h1 : 7 < Real.sqrt 61 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h2 : Real.sqrt 61 < 8 := by
          rw [Real.sqrt_lt] <;> norm_num
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try linarith)
        all_goals norm_num
        <;> nlinarith
      rw [h101]
      norm_num
      all_goals norm_num
      <;> nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num)]
    · -- Case x = Real.sqrt 71
      have h101 : ⌊(Real.sqrt 71 : ℝ)⌋ = 8 := by
        have h1 : 8 < Real.sqrt 71 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h2 : Real.sqrt 71 < 9 := by
          rw [Real.sqrt_lt] <;> norm_num
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try linarith)
        all_goals norm_num
        <;> nlinarith
      rw [h101]
      norm_num
      all_goals norm_num
      <;> nlinarith [Real.sqrt_nonneg 71, Real.sq_sqrt (show (0 : ℝ) ≤ (71 : ℝ) by norm_num)]
    · -- Case x = 9
      have h101 : ⌊(9 : ℝ)⌋ = 9 := by norm_num
      rw [h101]
      norm_num
      all_goals norm_num
      <;> nlinarith