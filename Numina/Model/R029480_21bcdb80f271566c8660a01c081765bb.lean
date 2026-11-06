import Mathlib

theorem calculus_16827 :
  {k : ℝ | Real.sqrt ((k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2) = 2 * Real.sqrt 13} = {-1} := by 
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if k satisfies the equation, then k = -1
    intro h_eq
    have h1 : Real.sqrt ((k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2) = 2 * Real.sqrt 13 := h_eq

    have h2 : (Real.sqrt ((k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2)) ^ 2 = (2 * Real.sqrt 13) ^ 2 := by
      rw [h1]

    have h3 : (Real.sqrt ((k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2)) ^ 2 = (k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2 := by
      apply Real.sq_sqrt
      positivity

    have h4 : (2 * Real.sqrt 13) ^ 2 = 52 := by 
      calc
        (2 * Real.sqrt 13) ^ 2 = 4 * (Real.sqrt 13) ^ 2 := by ring
        _ = 4 * (13) := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        _ = 52 := by norm_num

    rw [h3] at h2
    rw [h4] at h2

    have h5 : (k * 2 - 4) ^ 2 + (k * (-3) - 7) ^ 2 = 52 := h2

    -- Manipulate the quadratic
    have h6 : 13 * k ^ 2 + 26 * k + 13 = 0 := by
      nlinarith

    have h7 : (k + 1) ^ 2 = 0 := by 
      nlinarith

    have h8 : k + 1 = 0 := by
      apply pow_eq_zero 
      exact h7

    linarith

  · -- Backward direction: if k = -1, then it satisfies the equation
    intro h_eq
    have hk : k = -1 := by linarith
    rw [hk]
    have h1 : Real.sqrt ((-1 * 2 - 4 : ℝ) ^ 2 + (-1 * (-3) - 7 : ℝ) ^ 2) = 2 * Real.sqrt 13 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    linarith [h1]