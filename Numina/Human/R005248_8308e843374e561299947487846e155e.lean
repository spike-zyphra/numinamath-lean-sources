import Mathlib

/- Determine all natural numbers N such that \(2^N - 2N\) is a perfect square. -/
theorem number_theory_607142 : {N : ℕ | IsSquare (2^N - 2 * N : ℤ)} = {0, 1, 2} := by
  ext N
  -- Show that the solutions are \(N = 0, 1, 2\). First, observe that:
  -- \(2^0 - 0 = 1^2\), \(2^1 - 2 = 0^2\), and \(2^2 - 4 = 0^2\).
  -- Thus, the integers 0, 1, and 2 are solutions.
  constructor
  · simp
    intro hSquare
    -- Assume \(2^N - 2N\) is a perfect square, so there exists \(x \in \mathbb{N}\) such that \(2^N - 2N = x^2\).
    obtain ⟨x, hx⟩ := show ∃x : ℕ, (2^N - 2 * N : ℤ) = x^2 by
      rcases hSquare with ⟨x, hx⟩
      use x.natAbs
      simp
      linarith
    -- Check if \(N < 3\). If so, \(N\) must be 0, 1, or 2.
    by_cases hN: N < 3
    · omega
    simp at hN
    -- Assume by contradiction that there exists another integer \(N \geq 3\) that is a solution.
    -- Since \(2^N\) must be an integer, \(N \geq 0\), and thus \(N \geq 3\).
    -- Additionally, \(x\) must be divisible by 2, so \(x^2\) is divisible by 4.
    have hx₁ : 2 ∣ x := by
      have : 2 ∣ x * x := by
        suffices 2 ∣ (x : ℤ)^2 by
          norm_cast at this
          rw [pow_two] at this
          exact this
        rw [←hx]
        exact Int.dvd_sub (Dvd.dvd.pow (by rfl) (by linarith)) (by simp)
      have := (Prime.dvd_mul (Nat.Prime.prime (by norm_num))).mp this
      simp at this
      exact this
    -- Since \(N \geq 2\), \(2^N\) is also divisible by 4, and thus \(N\) must be even.
    have hN₂ : 2 ∣ N := by
      have hx₂ : 4 ∣ (x : ℤ)^2 := by
        rw [pow_two]; norm_cast
        rw [show 4 = 2^2 by simp, ←pow_two]
        exact pow_dvd_pow_of_dvd hx₁ 2
      rw [←hx] at hx₂
      have hN' : 4 ∣ 2^N := by
        rw [show 4 = 2^2 by simp]
        apply Nat.pow_dvd_pow 2
        linarith
      obtain ⟨k₁, hk₁⟩ := hx₂
      obtain ⟨k₂, hk₂⟩ := hN'
      have : 4 ∣ 2 * N := by
        have : 2 * N = 4 * k₂ - 4 * k₁ := by
          norm_cast
          rw [←hk₁, ←hk₂]
          simp
        suffices 4 ∣ (2 * N : ℤ) by norm_cast at this
        rw [this]
        apply Int.dvd_sub
        repeat apply Int.dvd_mul_right
      obtain ⟨k, hk⟩ := this
      use k
      omega
    -- Show that \(2^{N/2} + x \leq 2N\).
    have hN₃ : 2 ^ (N / 2) + x ≤ 2 * N := by
      have : 2 * N = (2 ^ (N / 2) + x) * (2 ^ (N / 2) - x : ℝ) := by
        ring_nf
        rw [Nat.div_mul_cancel hN₂, ←show 2 ^ N - 2 * N = (x : ℝ) ^ 2 by norm_cast; simp; rw [←hx]; norm_cast]
        ring_nf
      have : 2 ^ (N / 2) + x ≤ (2 * N : ℝ) := by
        rw [this, mul_comm]
        apply le_mul_of_one_le_left
        positivity
        by_contra! h'
        have hN₂ : 2 * (N : ℝ) ≤ 0 := by
          rw [this]; apply mul_nonpos_of_nonneg_of_nonpos
          positivity; norm_cast at h'; norm_cast; omega
        norm_cast at hN₂
        linarith
      norm_cast at this
    -- Show that \(2N < 2^{N/2} + x\) for \(N \geq 10\).
    have hN₄ : 2 * N < 2 ^ (N / 2) + x := by
      apply Nat.lt_add_right x
      have (n : ℕ) : 2 * (n + 10) < 2 ^ ((n + 10) / 2) := by
        induction' n using Nat.strongRec with n ih
        by_cases h: 2 ≤ n
        · specialize ih (n - 2) (by omega)
          rw [show (n + 10) / 2 = n / 2 + 5 by omega, pow_add]
          rw [show 2 * (n + 10) = 2 * n + 20 by omega]
          rw [show (n - 2 + 10) / 2 = n / 2 + 4 by omega, pow_add] at ih
          rw [show 2 * (n - 2 + 10) = 2 * n + 16 by omega] at ih
          apply lt_trans
          case pos.b => exact 2 ^ (n / 2) * 2 ^ 4 + 4
          linarith
          omega
        simp at h
        interval_cases n
        all_goals
          simp
      obtain ⟨r, hr⟩ := show ∃r, N = r + 10 by
        use N - 10
        apply Eq.symm (Nat.sub_add_cancel ?_)
        by_contra! hN₄
        interval_cases N
        all_goals norm_cast <;> simp at hSquare <;> absurd hSquare <;> native_decide
      specialize this r
      rw [←hr] at this
      exact this
    -- This leads to a contradiction, so no other solutions exist.
    linarith
  · simp
    rintro (hN | hN | hN)
    all_goals
      rw [hN]
      norm_num
