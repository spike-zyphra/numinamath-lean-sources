import Mathlib

theorem algebra_14564 : {b : ℝ | b + ⌈b⌉ = 17.8} = {8.8} := by
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume b + ⌈b⌉ = 17.8, prove b = 8.8
    intro h
    have h1 : (b : ℝ) + (⌈b⌉ : ℝ) = (17.8 : ℝ) := by
      simpa using h
    let n := ⌈b⌉
    have hn1 : n = ⌈b⌉ := by rfl
    have h2 : (n : ℝ) ≥ b := by
      exact Int.le_ceil b
    have h3 : (n : ℝ) < b + 1 := by
      exact Int.ceil_lt_add_one b
    have h4 : (b : ℝ) + (n : ℝ) = (17.8 : ℝ) := by
      simpa using h1
    have h5 : (b : ℝ) = (17.8 : ℝ) - (n : ℝ) := by
      linarith
    have h6 : (n : ℝ) ≥ (b : ℝ) := by
      exact Int.le_ceil b
    -- Now we can use our inequality and equation to derive the possible integer values of n
    -- Substituting b = 17.8 - n into n >= b
    have h7 : (n : ℝ) ≥ (8.9 : ℝ) := by
      nlinarith [h5, h6, h3]
    -- Now substituting into n < b + 1
    have h8 : (n : ℝ) < (9.4 : ℝ) := by
      nlinarith [h5, h3, h6]
    -- Convert to integer inequalities
    have hn2 : n = 9 := by
      have h9 : n ≥ 9 := by
        by_contra h
        push_neg at h
        have : n ≤ 8 := by omega
        have h10 : (n : ℝ) ≤ (8 : ℝ) := by exact_mod_cast this
        nlinarith
      have h10 : n ≤ 9 := by
        by_contra h
        push_neg at h
        have : n ≥ 10 := by omega
        have h11 : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast this
        nlinarith
      omega
    -- Now n = 9, from b = 17.8 - n, solving for b gives b = 8.8
    have h11 : (b : ℝ) = (8.8 : ℝ) := by
      have h12 : (n : ℝ) = (9 : ℝ) := by
        exact_mod_cast hn2
      nlinarith [h4, h12]
    linarith
  · -- Assume b = 8.8, prove b + ⌈b⌉ = 17.8
    intro h
    rw [h]
    norm_num [Int.ceil_eq_iff]