import Mathlib

theorem algebra_200342 {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (han : ∀ n, a (n + 1) = 2 * a n + Real.sqrt (3 * (a n)^2 + 1)) :
    ∀ n, ∃ m : ℤ, a n = m := by

  have h1 : ∀ n : ℕ, a (n + 2) = 4 * a (n + 1) - a n := by
    intro n
    have h1 : a (n + 2) = 2 * a (n + 1) + Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) := by
      specialize han (n + 1)
      simpa using han
    have h2 : a (n + 1) = 2 * a n + Real.sqrt (3 * (a n) ^ 2 + 1) := by
      specialize han n
      simpa using han

    have h3 : (a (n + 1) - 2 * a n) ^ 2 = 3 * (a n) ^ 2 + 1 := by
      have h4 : Real.sqrt (3 * (a n) ^ 2 + 1) = a (n + 1) - 2 * a n := by linarith [h2]
      have h13 : (Real.sqrt (3 * (a n) ^ 2 + 1)) ^ 2 = 3 * (a n) ^ 2 + 1 := by
        rw [Real.sq_sqrt]
        nlinarith [show 0 ≤ (3 * (a n) ^ 2 + 1 : ℝ) by nlinarith [sq_nonneg (a n)]]
      have h14 : (a (n + 1) - 2 * a n) ^ 2 = 3 * (a n) ^ 2 + 1 := by
        rw [show a (n + 1) - 2 * a n = Real.sqrt (3 * (a n) ^ 2 + 1) by linarith [h4]]
        nlinarith [h13]
      linarith

    have h4 : a (n + 1) ^ 2 - 4 * a (n + 1) * a n + a n ^ 2 - 1 = 0 := by
      nlinarith

    have h11 : Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) = 2 * a (n + 1) - a n := by
      have h13' : (2 * a (n + 1) - a n) ^ 2 = 3 * (a (n + 1)) ^ 2 + 1 := by
        nlinarith [h4]
      have h13 : (2 * a (n + 1) - a n) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (3 * (a n) ^ 2 + 1), sq_nonneg (a (n + 1) - a n), sq_nonneg (a (n + 1) - 2 * a n), sq_nonneg (a n - a (n + 1)), h2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (a n) ^ 2 + 1 by nlinarith), Real.sqrt_nonneg (3 * (a n) ^ 2 + 1)]
      have h14 : Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) = (2 * a (n + 1) - a n : ℝ) := by
        have h14' : (2 * a (n + 1) - a n : ℝ) ^ 2 = (3 * (a (n + 1)) ^ 2 + 1 : ℝ) := h13'
        have h15 : (2 * a (n + 1) - a n : ℝ) ≥ 0 := h13
        have h16 : Real.sqrt ((2 * a (n + 1) - a n : ℝ) ^ 2) = Real.sqrt ((3 * (a (n + 1)) ^ 2 + 1 : ℝ)) := by
          rw [h14']
        have h17 : Real.sqrt ((2 * a (n + 1) - a n : ℝ) ^ 2) = (2 * a (n + 1) - a n : ℝ) := by
          rw [Real.sqrt_sq (show 0 ≤ (2 * a (n + 1) - a n : ℝ) by linarith)]
        have h18 : Real.sqrt ((3 * (a (n + 1)) ^ 2 + 1 : ℝ)) = (2 * a (n + 1) - a n : ℝ) := by
          linarith [h16, h17]
        linarith [h18]

      linarith

    rw [h1]
    nlinarith [h11]

  -- Now we need to show that $a_0$ and $a_1$ are integers, and use the recurrence.
  have h8 : a 0 = (0 : ℝ) := by exact ha0
  have h9 : a 1 = (1 : ℝ) := by
    have h9 : a 1 = 2 * a 0 + Real.sqrt (3 * (a 0) ^ 2 + 1) := by exact han 0
    rw [show a 0 = (0 : ℝ) by exact ha0] at h9
    have h10 : Real.sqrt (3 * (0 : ℝ) ^ 2 + 1) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h10] at h9
    norm_num at h9 ⊢
    linarith

  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    use (0 : ℤ)
    norm_num [h8]
  | succ n =>
    cases n with
    | zero =>
      use (1 : ℤ)
      norm_num [h9]
    | succ n =>
      have h11 : ∃ m1 : ℤ, a n = m1 := ih n (by linarith)
      rcases h11 with ⟨m1, hm1⟩
      have h12 : ∃ m2 : ℤ, a (n + 1) = m2 := ih (n + 1) (by linarith)
      rcases h12 with ⟨m2, hm2⟩
      have h13 : a (n + 2) = 4 * a (n + 1) - a n := h1 n
      have h14 : (a (n + 2) : ℝ) = (4 * (a (n + 1) ) - (a n) ) := by
        linarith [h13]
      have h15 : (4 * (a (n + 1) ) - (a n) ) = (4 * (m2 : ℝ) - (m1 : ℝ) ) := by
        rw [show (a (n + 1)) = (m2 : ℝ) by linarith [hm2], show (a n) = (m1 : ℝ) by linarith [hm1] ]
      rw [h15] at h14
      have h16 : ∃ m3 : ℤ, (4 * (m2 : ℝ) - (m1 : ℝ) ) = m3 := by
        refine' ⟨4 * m2 - m1, by simp⟩
      rcases h16 with ⟨m3, hm3⟩
      use m3
      linarith [h14, hm3]