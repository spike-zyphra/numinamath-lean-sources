import Mathlib

theorem algebra_10331 : {n : ℝ | (2 : ℝ)^n * (4 : ℝ)^n = (64 : ℝ)^(n - 36)} = {72} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume that $2^n \cdot 4^n = 64^{n-36}$, prove that $n = 72$.
    intro h
    have h1 : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n : ℝ) := by
      calc
        (4 : ℝ) ^ n = ((2 : ℝ) ^ (2 : ℝ)) ^ n := by norm_num
        _ = (2 : ℝ) ^ (2 * n : ℝ) := by rw [← Real.rpow_mul]; ring; all_goals linarith
    have h2 : (64 : ℝ) ^ (n - 36 : ℝ) = (2 : ℝ) ^ (6 * (n - 36 : ℝ) : ℝ) := by
      calc
        (64 : ℝ) ^ (n - 36 : ℝ) = ((2 : ℝ) ^ (6 : ℝ)) ^ (n - 36 : ℝ) := by norm_num
        _ = (2 : ℝ) ^ (6 * (n - 36 : ℝ) : ℝ) := by rw [← Real.rpow_mul]; ring; all_goals linarith
    rw [h1] at h
    rw [h2] at h
    have h3 : (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (2 * n : ℝ) = (2 : ℝ) ^ (3 * n : ℝ) := by
      calc
        (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (2 * n : ℝ)
          = (2 : ℝ) ^ (n + 2 * n : ℝ) := by rw [← Real.rpow_add]; ring; all_goals linarith
        _ = (2 : ℝ) ^ (3 * n : ℝ) := by ring_nf
    rw [h3] at h
    have h4 : 3 * n = 6 * (n - 36) := by
      apply_fun (Real.logb (2 : ℝ)) at h
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * n : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (6 * (n - 36) : ℝ)) := by
        linarith
      have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * n : ℝ)) = 3 * n := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h7 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (6 * (n - 36) : ℝ)) = 6 * (n - 36) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h6] at h5
      rw [h7] at h5
      linarith
    linarith
  · -- Assume n = 72, prove the equation.
    intro h
    rw [h]
    have h1 : (2 : ℝ) ^ (72 : ℝ) * (4 : ℝ) ^ (72 : ℝ) = (64 : ℝ) ^ (72 - 36 : ℝ) := by
      have h2 : (4 : ℝ) ^ (72 : ℝ) = (2 : ℝ) ^ (144 : ℝ) := by
        calc
          (4 : ℝ) ^ (72 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (72 : ℝ) := by norm_num
          _ = (2 : ℝ) ^ (2 * (72 : ℝ) : ℝ) := by rw [← Real.rpow_mul]; ring; all_goals linarith
          _ = (2 : ℝ) ^ (144 : ℝ) := by norm_num
      have h3 : (64 : ℝ) ^ (72 - 36 : ℝ) = (2 : ℝ) ^ (216 : ℝ) := by
        calc
          (64 : ℝ) ^ (72 - 36 : ℝ) = ((2 : ℝ) ^ (6 : ℝ)) ^ (72 - 36 : ℝ) := by norm_num
          _ = (2 : ℝ) ^ (6 * (72 - 36 : ℝ) : ℝ) := by rw [← Real.rpow_mul]; ring; all_goals linarith
          _ = (2 : ℝ) ^ (216 : ℝ) := by norm_num
      calc
        (2 : ℝ) ^ (72 : ℝ) * (4 : ℝ) ^ (72 : ℝ)
            = (2 : ℝ) ^ (72 : ℝ) * (2 : ℝ) ^ (144 : ℝ) := by rw [h2]
        _ = (2 : ℝ) ^ (72 + 144 : ℝ) := by rw [← Real.rpow_add]; ring; all_goals linarith
        _ = (2 : ℝ) ^ (216 : ℝ) := by norm_num
        _ = (64 : ℝ) ^ (72 - 36 : ℝ) := by rw [h3]
    linarith