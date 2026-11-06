import Mathlib

theorem algebra_288896 {a : ℕ → ℝ}
    (ha1 : a 1 = Real.sqrt 2 / 2 + 1)
    (ha2 : a 2 = Real.sqrt 2 + 1)
    (han : ∀ n ≥ 2, a (n + 1) + a (n - 1) = n / (a n - a (n - 1)) + 2) :
    ∀ n ≥ 1, a n = n / Real.sqrt 2 + 1 := by 
  intro n hn
  have h1 : ∀ n ≥ 1, a n = n / Real.sqrt 2 + 1 := by
    intro n hn 
    induction' n using Nat.strongRecOn with n ih
    cases n with 
    | zero => 
      linarith 
    | succ n => 
      cases n with
      | zero => 
        rw [ha1]
        field_simp 
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      | succ n => 
        cases n with 
        | zero => 
          rw [ha2]
          field_simp
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        | succ n => 
          have h7 := ih (n + 1) (by linarith) (by linarith)
          have h8 := ih (n + 2) (by linarith) (by linarith)
          have h11 := han (n + 2) (by linarith)
          simp [show n + 2 + 1 = n + 3 by omega, show n + 2 - 1 = n + 1 by omega] at h11
          norm_num at h7 h8 h11 ⊢
          rw [show a (n + 1) = (↑n + 1) / Real.sqrt 2 + 1 by linarith [h7]] at h11 
          rw [show a (n + 2) = (↑n + 2) / Real.sqrt 2 + 1 by linarith [h8]] at h11
          field_simp [(show Real.sqrt 2 ≠ 0 by positivity)] at h11 ⊢ 
          <;> ring_nf at h11 ⊢
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
  specialize h1 n hn 
  simpa using h1