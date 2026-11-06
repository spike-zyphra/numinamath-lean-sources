import Mathlib

theorem algebra_94785 {M N : ℝ} (hMN : M ≠ N) (hM : 0 < M) (hN : 0 < N)
    (hM1 : M ≠ 1) (hN1 : N ≠ 1) (h : Real.logb M N = Real.logb N M) :
    M * N = 1 := by
  have h1 : Real.logb M N = Real.log N / Real.log M := by
    field_simp [Real.logb]
  have h2 : Real.logb N M = Real.log M / Real.log N := by
    field_simp [Real.logb]
  rw [h1] at h
  rw [h2] at h
  have hM0 : Real.log M ≠ 0 := by
    have hM2 : M > 0 := hM
    have hM3 : M ≠ 1 := hM1
    exact Real.log_ne_zero_of_pos_of_ne_one hM2 hM3
  have hN0 : Real.log N ≠ 0 := by
    have hN2 : N > 0 := hN
    have hN3 : N ≠ 1 := hN1
    exact Real.log_ne_zero_of_pos_of_ne_one hN2 hN3
  have h3 : (Real.log N) ^ 2 = (Real.log M) ^ 2 := by
    field_simp [hM0, hN0] at h ⊢
    nlinarith
  have h4 : Real.log N = Real.log M ∨ Real.log N = -Real.log M := by
    have h5 : (Real.log N) ^ 2 = (Real.log M) ^ 2 := h3
    have : (Real.log N - Real.log M) * (Real.log N + Real.log M) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h6 h7
    · left
      linarith
    · right
      linarith
  cases h4 with
  | inl h5 =>
    have h6 : N = M := by
      have h7 : Real.log N = Real.log M := h5
      have h8 : N > 0 := hN
      have h9 : M > 0 := hM
      have h10 : N = M := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h7
      linarith
    have h7 : M = N := by linarith [h6]
    contradiction
  | inr h6 =>
    have h7 : Real.log N + Real.log M = 0 := by
      linarith [h6]
    have h8 : Real.log (M * N) = 0 := by
      have h9 : Real.log (M * N) = Real.log M + Real.log N := by
        rw [Real.log_mul (by linarith) (by linarith)]
      linarith [h7, h9]
    have h9 : M * N > 0 := by
      nlinarith
    have h10 : Real.log (M * N) = Real.log 1 := by
      rw [h8]
      simp
    have h11 : M * N = 1 := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (show 0 < M * N by nlinarith)) (Set.mem_Ioi.mpr (show 0 < 1 by norm_num)) h10
    exact h11