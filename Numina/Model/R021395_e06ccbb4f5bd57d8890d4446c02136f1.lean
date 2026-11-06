import Mathlib

theorem algebra_299626 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (M N : ℝ) (hM : 0 < M) (hN : 0 < N) :
    Real.logb a (M * N) = Real.logb a M + Real.logb a N := by
  have h1 : 0 < a := ha.1
  have h2 : a ≠ 1 := ha.2
  have h3 : 0 < M := hM
  have h4 : 0 < N := hN
  have h5 : Real.logb a (M * N) = Real.log (M * N) / Real.log a := by 
    field_simp [Real.logb]
  have h6 : Real.logb a M = Real.log M / Real.log a := by 
    field_simp [Real.logb]
  have h7 : Real.logb a N = Real.log N / Real.log a := by 
    field_simp [Real.logb]
  have h8 : Real.log (M * N) = Real.log M + Real.log N := by 
    rw [Real.log_mul (by linarith) (by linarith)]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  have h9 : Real.log a ≠ 0 := by 
    have ha1 : 0 < a := h1
    have ha2 : a ≠ 1 := h2
    have h9 : Real.log a ≠ 0 := by 
      by_contra h 
      have h10 : a = 1 := by 
        have h11 : Real.log a = 0 := h
        have h12 : a = 1 := by 
          rw [Real.log_eq_zero] at h11 
          rcases h11 with (r | r | r)
          · linarith 
          · linarith 
          · linarith 
        exact h12 
      contradiction 
    exact h9 
  field_simp [h9]
  <;> ring