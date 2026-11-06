import Mathlib

theorem algebra_282112 :
  {x : ℝ | (3 : ℝ)^(2*x) + (3 : ℝ)^(2*x - 1) = 
           (2 : ℝ)^(x + 7/2) + (2 : ℝ)^(x + 1/2)} = 
  {3/2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ {x | 3^(2x) + 3^(2x-1) = 2^(x+7/2) + 2^(x+1/2)}, prove x = 3/2
    intro h
    have h1 : (3 : ℝ) ^ (2 * x) + (3 : ℝ) ^ (2 * x - 1) = (2 : ℝ) ^ (x + 7 / 2) + (2 : ℝ) ^ (x + 1 / 2) := by
      linarith
    have eq1 : (3 : ℝ) ^ (2 * x) + (3 : ℝ) ^ (2 * x - 1) = 4 * ((3 : ℝ) ^ (2 * x - 1 : ℝ)) := by
      have h2 : (3 : ℝ) ^ (2 * x : ℝ) = (3 : ℝ) ^ ((2 * x - 1 : ℝ) + 1) := by ring_nf
      rw [h2]
      have h3 : (3 : ℝ) ^ ((2 * x - 1 : ℝ) + 1) = (3 : ℝ) ^ (2 * x - 1 : ℝ) * (3 : ℝ) ^ (1 : ℝ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h3]
      norm_num
      all_goals ring_nf
    have eq2 : (2 : ℝ) ^ (x + 7 / 2 : ℝ) + (2 : ℝ) ^ (x + 1 / 2 : ℝ) = 9 * ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) := by
      have h2 : (2 : ℝ) ^ (x + 7 / 2 : ℝ) = (2 : ℝ) ^ (x + 1 / 2 : ℝ) * (2 ^ (3 : ℝ)) := by
        have h3 : (x + 7 / 2 : ℝ) = (x + 1 / 2 : ℝ) + (3 : ℝ) := by linarith
        rw [h3]
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      have h4 : (2 : ℝ) ^ (3 : ℝ) = (8 : ℝ) := by norm_num
      rw [h2, h4]
      all_goals ring_nf
    rw [eq1, eq2] at h1
    have eq3 : 4 * ((3 : ℝ) ^ (2 * x - 1 : ℝ)) = 9 * ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) := by
      linarith
    have eq4 : Real.log (4 * ((3 : ℝ) ^ (2 * x - 1 : ℝ)) ) = Real.log (9 * ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) ) := by
      rw [eq3]
    have eq5 : Real.log (4 * ((3 : ℝ) ^ (2 * x - 1 : ℝ)) ) = Real.log 4 + Real.log ((3 : ℝ) ^ (2 * x - 1 : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have eq6 : Real.log ((3 : ℝ) ^ (2 * x - 1 : ℝ)) = (2 * x - 1 : ℝ) * Real.log 3 := by
      rw [Real.log_rpow]
      all_goals linarith
    have eq7 : Real.log (9 * ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) ) = Real.log 9 + Real.log ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have eq8 : Real.log ((2 : ℝ) ^ (x + 1 / 2 : ℝ)) = (x + 1 / 2 : ℝ) * Real.log 2 := by
      rw [Real.log_rpow]
      all_goals linarith
    rw [eq5, eq6, eq7, eq8] at eq4
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    have h4 : Real.log 9 = 2 * Real.log 3 := by
      calc
        Real.log 9 = Real.log (3 ^ 2) := by norm_num
        _ = 2 * Real.log 3 := by simp [Real.log_pow]
    have eq9 : (2 * Real.log 3 - Real.log 2) * (x - 3 / 2) = 0 := by
      nlinarith [eq4, h3, h4]
    cases' (mul_eq_zero.mp eq9) with h5 h6
    · 
      have h7 : 2 * Real.log 3 - Real.log 2 = 0 := by linarith
      have h8 : Real.log 9 = Real.log 2 := by
        have h7' : 2 * Real.log 3 = Real.log 2 := by linarith
        have h9 : Real.log 9 = 2 * Real.log 3 := by
          calc
            Real.log 9 = Real.log (3 ^ 2) := by norm_num
            _ = 2 * Real.log 3 := by simp [Real.log_pow]
        linarith [h7', h9]
      have h10 : (9 : ℝ) = (2 : ℝ) := by
        have h11 : Real.log 9 = Real.log 2 := h8
        have h12 : (9 : ℝ) > 0 := by norm_num
        have h13 : (2 : ℝ) > 0 := by norm_num
        have h14 : (9 : ℝ) = (2 : ℝ) := by
          exact Real.log_injOn_pos (Set.mem_Ioi.mpr h12) (Set.mem_Ioi.mpr h13) h11
        linarith
      linarith
    · 
      linarith
  · -- Assume x = 3/2, prove 3^(2x) + 3^(2x-1) = 2^(x+7/2) + 2^(x+1/2)
    intro h
    rw [h]
    have h1 : (3 : ℝ) ^ (2 * (3 / 2 : ℝ) : ℝ) = (27 : ℝ) := by
      norm_num
    have h2 : (3 : ℝ) ^ (2 * (3 / 2 : ℝ) - 1 : ℝ) = (9 : ℝ) := by
      norm_num
    have h3 : (2 : ℝ) ^ ((3 / 2 : ℝ) + 7 / 2 : ℝ) = (32 : ℝ) := by
      norm_num
    have h4 : (2 : ℝ) ^ ((3 / 2 : ℝ) + 1 / 2 : ℝ) = (4 : ℝ) := by
      norm_num
    rw [h1, h2, h3, h4]
    all_goals norm_num