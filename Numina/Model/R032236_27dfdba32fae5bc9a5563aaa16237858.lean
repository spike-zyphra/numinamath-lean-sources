import Mathlib

theorem algebra_16021 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 2 n, i * 2 ^ i = 2 ^ (n + 10) ↔ n = 513 := by
  constructor
  · -- Assume the sum equals $2^{n+10}$, prove $n = 513$.
    intro h
    have h1 : n ≥ 2 := by
      by_contra h1
      push_neg at h1
      have h2 : n = 1 := by linarith
      rw [h2] at h
      norm_num [Finset.sum_eq_zero] at h
    have h2 : ∀ (n : ℕ), n ≥ 2 → ∑ i in Finset.Icc 2 n, i * 2 ^ i = (n - 1) * 2 ^ (n + 1 : ℕ) := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => linarith
        | succ n =>
          cases n with
          | zero =>
            norm_num [Finset.sum_Icc_succ_top] at ih ⊢
          | succ n =>
            simp [Finset.sum_Icc_succ_top, mul_add, pow_succ, Nat.add_sub_cancel] at ih ⊢
            ring_nf at ih ⊢
            omega
    have h3 : ∑ i in Finset.Icc 2 n, i * 2 ^ i = (n - 1) * 2 ^ (n + 1 : ℕ) := h2 n (by omega)
    rw [h3] at h
    have eq1 : (n - 1 : ℕ) * 2 ^ (n + 1 : ℕ) = 2 ^ (n + 10 : ℕ) := by
      exact_mod_cast h
    have eq2 : n = 513 := by
      have eq3 : (n - 1 : ℕ) * 2 ^ (n + 1 : ℕ) = 2 ^ (n + 10 : ℕ) := eq1
      have eq4 : n ≥ 2 := h1
      have eq5 : 2 ^ (n + 10 : ℕ) = 2 ^ (n + 1 : ℕ) * 512 := by
        have eq6 : 2 ^ (n + 10 : ℕ) = 2 ^ (n + 1 : ℕ) * (2 ^ 9 : ℕ) := by
          ring_nf
        rw [eq6]
        all_goals norm_num
      rw [eq5] at eq3
      have eq7 : (n - 1 : ℕ) = 512 := by
        have eq8 : 2 ^ (n + 1 : ℕ) > 0 := by
          apply Nat.pow_pos
          norm_num
        have eq9 : (n - 1 : ℕ) * 2 ^ (n + 1 : ℕ) = 2 ^ (n + 1 : ℕ) * 512 := by 
          linarith
        have eq10 : (n - 1 : ℕ) = 512 := by
          have eq11 : 2 ^ (n + 1 : ℕ) > 0 := eq8
          apply (mul_left_inj' (show 2 ^ (n + 1 : ℕ) ≠ 0 by omega)).mp
          linarith
        exact eq10
      omega
    exact_mod_cast eq2
  · -- Assume n = 513, prove the sum equals 2^(n+10).
    intro h
    rw [h]
    have h3 : ∀ (n : ℕ), n ≥ 2 → ∑ i in Finset.Icc 2 n, i * 2 ^ i = (n - 1) * 2 ^ (n + 1 : ℕ) := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero => linarith
        | succ n =>
          cases n with
          | zero =>
            norm_num [Finset.sum_Icc_succ_top] at ih ⊢
          | succ n =>
            simp [Finset.sum_Icc_succ_top, mul_add, pow_succ, Nat.add_sub_cancel] at ih ⊢
            ring_nf at ih ⊢
            omega
    have h4 : ∑ i in Finset.Icc 2 513, i * 2 ^ i = (513 - 1 : ℕ) * 2 ^ (513 + 1 : ℕ) := by
      apply h3 513
      all_goals norm_num
    rw [h4]
    all_goals norm_num