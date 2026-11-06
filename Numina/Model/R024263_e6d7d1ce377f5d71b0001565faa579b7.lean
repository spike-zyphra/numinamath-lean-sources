import Mathlib

theorem algebra_20341 : {c : ℝ | Complex.abs (3 - c * .I) = 7}.encard = 2 := by 
  have h1 : {c : ℝ | Complex.abs (3 - c * .I) = 7} = {Real.sqrt 40, -Real.sqrt 40} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- If |3 - ci| = 7, then c = ±√40.
      intro h
      have h2 : Complex.abs (3 - c * Complex.I) = Real.sqrt (9 + c^2) := by
        simp [Complex.abs, Complex.normSq]
        ring
      rw [h2] at h 
      have h3 : 9 + c ^ 2 = 49 := by
        calc
          9 + c ^ 2 = (Real.sqrt (9 + c^2)) ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          _ = 7 ^ 2 := by 
            rw [h]
          _ = 49 := by
            norm_num
      have h4 : c^2 = 40 := by 
        linarith
      have h5 : c = Real.sqrt 40 ∨ c = -Real.sqrt 40 := by 
        have h6 : (c - Real.sqrt 40) * (c + Real.sqrt 40) = 0 := by
          have h7 : c^2 = 40 := h4
          nlinarith [Real.sqrt_nonneg 40, Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num)]
        cases' (mul_eq_zero.mp h6) with h8 h9
        · -- Case c - Real.sqrt 40 = 0
          left
          linarith 
        · -- Case c + Real.sqrt 40 = 0
          right
          linarith 
      tauto 
    · -- If c = ±√40, then |3 - ci| = 7.
      rintro (h | h)
      · -- Case c = Real.sqrt 40.
        rw [h]
        have h2 : Complex.abs (3 - (Real.sqrt 40) * Complex.I) = Real.sqrt (9 + (Real.sqrt 40) ^ 2) := by
          simp [Complex.abs, Complex.normSq]
          <;> ring
        rw [h2]
        have h3 : (9 + (Real.sqrt 40) ^ 2) = (49 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (40 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num)]
        rw [h3]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      · -- Case c = -Real.sqrt 40.
        rw [h]
        have h2 : Complex.abs (3 - ↑(-Real.sqrt 40) * Complex.I) = Real.sqrt (9 + (-Real.sqrt 40) ^ 2) := by
          simp [Complex.abs, Complex.normSq]
          <;> ring_nf
        rw [h2]
        have h3 : (9 + (-Real.sqrt 40) ^ 2) = (49 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (40 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num)]
        rw [h3]
        exact Real.sqrt_eq_cases.2 (by norm_num)
  rw [h1]
  have h2 : Real.sqrt 40 > 0 := by
    apply Real.sqrt_pos.mpr 
    norm_num
  rw [Set.encard_pair (by
    -- Show Real.sqrt 40 ≠ -Real.sqrt 40
    intro h 
    nlinarith [h2]
  )]
  all_goals 
    norm_num