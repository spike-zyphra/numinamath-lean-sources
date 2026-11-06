import Mathlib

theorem algebra_9153 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han : ∀ n, ∃! x, x^2 - a (n + 1) * Real.cos x + 2 * a n + 1 = 0) :
    ∀ n, a n = 2 ^ n - 1 := by
  have h10 := han 0 
  rcases h10 with ⟨x, ⟨hx11, hx22⟩⟩
  have h4 : x = 0 := by
    have hx5 : (-x) ^ 2 - a (0 + 1) * Real.cos (-x) + 2 * a 0 + 1 = 0 := by 
      have eq1 : (-x) ^ 2 - a (0 + 1) * Real.cos (-x) + 2 * a 0 + 1 = 0 := by 
        have h5 : x ^ 2 - a (0 + 1) * Real.cos x + 2 * a 0 + 1 = 0 := by
          simpa using hx11
        have h7 : (-x : ℝ) ^ 2 = x ^ 2 := by ring 
        have h8 : Real.cos (-x) = Real.cos x := Real.cos_neg x 
        rw [h7, h8] at *
        all_goals 
          linarith 
      assumption 
    have hx6 : -x = x := by
      apply hx22 
      simpa using hx5
    linarith
  have h41 : a 0 = 0 := by
    have h5 : x ^ 2 - a (0 + 1) * Real.cos x + 2 * a 0 + 1 = 0 := by 
      simpa using hx11
    rw [show x = (0 : ℝ) by linarith [h4]] at h5
    norm_num [ha1] at h5 ⊢
    all_goals linarith 
  have h22 : ∀ n, a (n + 1) = 2 * a n + 1 := by 
    intro n 
    have h1n := han n 
    rcases h1n with ⟨x, ⟨hx11n, hx22n⟩⟩ 
    have h4n : x = 0 := by 
      have hx5n : (-x) ^ 2 - a (n + 1) * Real.cos (-x) + 2 * a n + 1 = 0 := by 
        have eq1 : (-x) ^ 2 - a (n + 1) * Real.cos (-x) + 2 * a n + 1 = 0 := by 
          have h5n : x ^ 2 - a (n + 1) * Real.cos x + 2 * a n + 1 = 0 := by 
            simpa using hx11n 
          have h7 : (-x : ℝ) ^ 2 = x ^ 2 := by ring 
          have h8 : Real.cos (-x) = Real.cos x := Real.cos_neg x 
          rw [h7, h8] at *
          all_goals 
            linarith 
        assumption 
      have hx6n : -x = x := by 
        apply hx22n 
        simpa using hx5n 
      linarith 
    have eq11n : a (n + 1) = 2 * a n + 1 := by 
      have h5n : x ^ 2 - a (n + 1) * Real.cos x + 2 * a n + 1 = 0 := by 
        simpa using hx11n 
      rw [show x = (0 : ℝ) by linarith [h4n]] at h5n 
      norm_num [Real.cos_zero] at h5n ⊢ 
      linarith 
    simpa using eq11n 
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    rw [show a 0 = (0 : ℝ) by linarith [h41]]
    norm_num
  | succ n =>
    cases n with 
    | zero => 
      rw [show a 1 = (1 : ℝ) by linarith [ha1]]
      norm_num 
    | succ n => 
      have ih1 := ih (n + 1) (by linarith)
      have h11 : a (n + 2) = 2 * a (n + 1) + 1 := by 
        specialize h22 (n + 1) 
        simpa using h22 
      rw [show n + 2 = (n + 1) + 1 by omega]
      rw [h11] 
      rw [ih1] 
      simp [pow_add, pow_mul] 
      <;> ring_nf <;> norm_num