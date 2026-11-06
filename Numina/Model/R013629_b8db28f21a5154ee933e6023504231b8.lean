import Mathlib

open Real

/- If $N$ is a natural number, and $N  <  {(\sqrt{3}+\sqrt{2})}^{6}  <  N+1$, then the value of $N$ is （   ） . ( Mini English-Chinese Dictionary: natural number: 自然数)

If $N$ is a natural number, and $N  <  {(\sqrt{3}+\sqrt{2})}^{6}  <  N+1$, then the value of $N$ is ___          ___ . -/
theorem number_theory_1716 {N : ℕ} (hN : N < (sqrt 3 + sqrt 2)^6 ∧ (sqrt 3 + sqrt 2)^6 < N + 1) :
    N = 969 := by
  have h1 : (sqrt 3 + sqrt 2: ℝ) ^ 2 = 5 + 2 * Real.sqrt 6 := by
    calc
      (sqrt 3 + sqrt 2: ℝ) ^ 2 = (sqrt 3) ^ 2 + (sqrt 2) ^ 2 + 2 * (sqrt 3 * sqrt 2) := by ring
      _ = 3 + 2 + 2 * (sqrt 3 * sqrt 2) := by simp [Real.sq_sqrt]
      _ = 5 + 2 * (sqrt 3 * sqrt 2) := by ring
      _ = 5 + 2 * Real.sqrt 6 := by
        have h : sqrt 3 * sqrt 2 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num)]
          all_goals norm_num
        rw [h]
  have h2 : (sqrt 3 + sqrt 2: ℝ) ^ 4 = (5 + 2 * Real.sqrt 6) ^ 2 := by
    calc
      (sqrt 3 + sqrt 2: ℝ) ^ 4 = ((sqrt 3 + sqrt 2: ℝ) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * Real.sqrt 6) ^ 2 := by rw [h1]
  have h3 : (sqrt 3 + sqrt 2: ℝ) ^ 4 = 49 + 20 * Real.sqrt 6 := by
    rw [h2]
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  have h4 : (sqrt 3 + sqrt 2: ℝ) ^ 6 = ((sqrt 3 + sqrt 2: ℝ) ^ 4) * ((sqrt 3 + sqrt 2: ℝ) ^ 2) := by ring
  have h5 : (sqrt 3 + sqrt 2: ℝ) ^ 6 = (485 + 198 * Real.sqrt 6) := by
    rw [h4, h3, h1]
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  have h6 : (sqrt 3 + sqrt 2: ℝ) ^ 6 > (969 : ℝ) := by
    rw [h5]
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  have h7 : (sqrt 3 + sqrt 2: ℝ) ^ 6 < (970 : ℝ) := by
    rw [h5]
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (by norm_num : (6 : ℝ) > (0 : ℝ) ) ]
  have h8 : N < 970 := by
    by_contra h
    push_neg at h
    have h11 : N ≥ 970 := by
      omega
    have h12 : (N : ℝ) ≥ (970 : ℝ) := by
      exact_mod_cast h11
    nlinarith [h7, hN.1]
  have h11 : N > 968 := by
    by_contra h
    push_neg at h
    have h12 : N ≤ 968 := by
      omega
    have h13 : (N : ℝ) ≤ (968 : ℝ) := by
      exact_mod_cast h12
    nlinarith [h6, hN.2]
  have h14 : N = 969 := by
    omega
  exact_mod_cast h14