import Mathlib

theorem number_theory_271175 : {x : ℤ | x > -Real.sqrt 8 ∧ x < Real.sqrt 32}.encard = 8 := by
  have h4 : {x : ℤ | x > -Real.sqrt 8 ∧ x < Real.sqrt 32} = {-2, -1, 0, 1, 2, 3, 4, 5} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h in left side, prove in right side
      intro h
      rcases h with ⟨h1, h2⟩
      have h5 : n > -3 := by
        by_contra h
        push_neg at h
        have h6 : n ≤ -3 := by omega
        have h7 : (n : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h6
        have h1' : (n : ℝ) > -Real.sqrt 8 := by exact_mod_cast h1
        have h4 : Real.sqrt 8 > (2 : ℝ) := by
          have h3 : Real.sqrt 8 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
          linarith
        nlinarith [show Real.sqrt 8 > 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
      have h6 : n < 6 := by
        by_contra h
        push_neg at h
        have h7 : n ≥ 6 := by omega
        have h8 : (n : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h7
        have h2' : (n : ℝ) < (Real.sqrt 32 : ℝ) := by exact_mod_cast h2
        have h5 : Real.sqrt 32 < (6 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 32, Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)]
        nlinarith [show Real.sqrt 32 > 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)]
      have h66 : n ≥ -2 := by
        by_contra h
        push_neg at h
        have h7 : n < -2 := by omega
        have h8 : (n : ℝ) < (-2 : ℝ) := by exact_mod_cast h7
        have h1' : (n : ℝ) > (-Real.sqrt 8 : ℝ) := by exact_mod_cast h1
        have h4 : Real.sqrt 8 > (2 : ℝ) := by
          have h3 : Real.sqrt 8 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
          linarith
        nlinarith [show Real.sqrt 8 > 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
      have h88 : n ≤ 5 := by
        by_contra h
        push_neg at h
        have h9 : n > 5 := by omega
        have h10 : (n : ℝ) > (5 : ℝ) := by exact_mod_cast h9
        have h2' : (n : ℝ) < (Real.sqrt 32 : ℝ) := by exact_mod_cast h2
        have h5 : Real.sqrt 32 < (6 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 32, Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)]
        nlinarith [show Real.sqrt 32 > 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)]
      interval_cases n <;> norm_num at h1 h2 ⊢
    · -- Assume h in right side, prove in left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · -- Show $-2 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (-2 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (-2 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $-2 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (-2 : ℝ) < √32.
          have h6' : (-2 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (-2 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $-1 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (-1 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (-1 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $-1 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (-1 : ℝ) < √32.
          have h6' : (-1 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (-1 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $0 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (0 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (0 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $0 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (0 : ℝ) < √32.
          have h6' : (0 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (0 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $1 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (1 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (1 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $1 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (1 : ℝ) < √32.
          have h6' : (1 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (1 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $2 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (2 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (2 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $2 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (2 : ℝ) < √32.
          have h6' : (2 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (2 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $3 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (3 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (3 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $3 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (3 : ℝ) < √32.
          have h6' : (3 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (3 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $4 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (4 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (4 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $4 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (4 : ℝ) < √32.
          have h6' : (4 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (4 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
      · constructor
        · -- Show $5 > -Real.sqrt 8$
          have h1 : -Real.sqrt 8 < (5 : ℝ) := by
            have h4 : Real.sqrt 8 > (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
            linarith
          exact_mod_cast (show (5 : ℤ) > -Real.sqrt 8 by exact_mod_cast h1)
        · -- Show $5 < Real.sqrt 32$
          -- First establish that Real.sqrt 32 > 0 
          have h4' : Real.sqrt 32 > (0 : ℝ) := by positivity
          have h5' : Real.sqrt 32 > (0 : ℝ) := h4'
          -- Goal (5 : ℝ) < √32.
          have h6' : (5 : ℝ) < Real.sqrt 32 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sqrt_nonneg 32, h4']
          exact_mod_cast (show (5 : ℤ) < Real.sqrt 32 by
            exact_mod_cast h6')
  rw [h4]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> aesop