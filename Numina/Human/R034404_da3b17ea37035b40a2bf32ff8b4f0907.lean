import Mathlib

/- Determine all pairs $(m, n)$ of positive integers such that $2^{m}-1=3^{n}$ -/
theorem number_theory_126604 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (h : 2^m - 1 = 3^n) : (m, n) = (2, 1) := by
  -- Observe $3^n$ mod $8$ alternates between $1$ and $3$.
  have h_3n_mod_8 : 3^n % 8 = if n % 2 = 0 then 1 else 3 := by
    induction n with
    | zero =>
      simp [Nat.pow_zero]
    | succ n ih =>
      have h1 : 3^(n + 1) = 3 * 3^n := by simp [Nat.pow_succ, mul_comm]
      rw [h1, Nat.mul_mod]
      have h2 : 3 % 8 = 3 := by norm_num
      rw [h2]
      have h3 : (n + 1) % 2 = (n % 2 + 1) % 2 := by rw [Nat.add_mod]
      rw [h3]
      by_cases h_n : n % 2 = 0
      · -- case :$n$ is even.
        have h_n_mod : (n % 2 + 1) % 2 = 1 := by rw [h_n]
        rw [h_n_mod]
        simp
        have h_3n : 3^n % 8 = 1 := by
          by_cases h_n_zero : n = 0
          · subst h_n_zero; norm_num
          · have h_n_pos : n > 0 := by omega
            let k := n / 2
            have h_n_div : n = 2 * k := by omega
            rw [h_n_div, Nat.pow_mul]
            simp [Nat.pow_two]
            have h_9k : 9^k % 8 = 1 := by
              induction k with
              | zero => norm_num
              | succ k' ih' =>
                omega
            exact h_9k
        omega
      · -- case :$n$ is odd.
        have h_n_eq_1 : n % 2 = 1 := by omega
        have h_n_mod : (n % 2 + 1) % 2 = 0 := by rw [h_n_eq_1]
        rw [h_n_mod]
        simp
        have h_3n : 3^n % 8 = 3 := by
          have h_n_pos : n > 0 := by omega
          let k := n / 2
          have h_n_div : n = 2 * k + 1 := by omega
          rw [h_n_div, Nat.pow_add, Nat.pow_mul]
          simp [Nat.pow_two, Nat.pow_one]
          induction k with
          | zero => norm_num
          | succ k' ih' =>
            omega
        omega

  -- If $m ≥ 3$, then $2^m - 1 ≡ 7 mod 8$, contradicting $3^n ≡ 1 or 3 mod 8$.
  have h_m_lt_3 : m < 3 := by
    by_contra h_m_ge_3
    have : m ≥ 3 := by exact Nat.le_of_not_lt h_m_ge_3
    have h_2m_mod_8 : 2^m % 8 = 0 := by
      have : m ≥ 3 := by exact this
      have : 2^3 = 8 := by norm_num
      have : 2^m = 2^(m - 3) * 2^3 := by
        have : (m - 3) + 3 = m := by omega
        have : 2^m = 2^((m - 3) + 3) := by rw [this]
        rw [Nat.pow_add] at this
        exact this
      rw [this, Nat.mul_mod]
      have : 2^3 % 8 = 0 := by norm_num
      norm_num
    have : (2^m - 1) % 8 = 7 := by
      have h1 : 2^m ≡ 0 [MOD 8] := by exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mod_eq_zero h_2m_mod_8)
      have h2 : 2^m + 7 ≡ 7 [MOD 8] := by
        have : 2^m + 7 ≡ 0 + 7 [MOD 8] := by
          apply Nat.ModEq.add
          exact h1
          exact Nat.ModEq.refl 7
        exact this
      have h3 : 2^m + 7 ≡ 2^m - 1 + 8 [MOD 8] := by
        have : 2 ^ m - 1 + 8 = 2 ^ m + 7 := by
          rw [← Nat.sub_add_cancel (Nat.one_le_pow m 2 (by norm_num))]
          exact rfl
        rw [this]
      have h4 : 2^m - 1 + 8 ≡ 2^m - 1 [MOD 8] := by
        let a := 2 ^ m - 1
        have : (a + 8) % 8 = a % 8 := by
          rw [Nat.add_mod, Nat.mod_self]
          norm_num
        exact this
      have h5 : 2^m + 7 ≡ 2^m - 1 [MOD 8] := by
        exact Nat.ModEq.trans h3 (Nat.ModEq.symm h4.symm)
      have h6 : 2^m - 1 ≡ 7 [MOD 8] := by
        exact Nat.ModEq.trans h5.symm (Nat.ModEq.symm h2.symm)
      exact h6
    have : 3^n % 8 = 7 := by
      rw [← h]
      exact this
    have : 3^n % 8 = if n % 2 = 0 then 1 else 3 := h_3n_mod_8
    split_ifs at this with h_n
    · have : 1 = 7 := by linarith
      contradiction
    · have : 3 = 7 := by linarith
      contradiction

  -- Since $m ≥ 1$ and $m < 3$, $m = 1$ or $m = 2$.
  have h_m_cases : m = 1 ∨ m = 2 := by omega

  -- Check $m = 1$.
  have h_m_eq_1 : m = 1 → False := by
    intro h_m_eq_1
    rw [h_m_eq_1] at h
    have : 2^1 - 1 = 1 := by norm_num
    rw [this] at h
    have : 3^n = 1 := by exact h.symm
    have : n = 0 := by
      cases n with
      | zero => simp
      | succ n =>
        have : 3^(n + 1) ≥ 3 := by omega
        linarith
    have : n ≥ 1 := by omega
    linarith

  -- Check $m = 2$.
  have h_m_eq_2 : m = 2 → (m, n) = (2, 1) := by
    intro h_m_eq_2
    rw [h_m_eq_2] at h
    have : 2^2 - 1 = 3 := by norm_num
    rw [this] at h
    have : 3^n = 3 := by exact h.symm
    have : n = 1 := by
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          have : 3^(n + 2) ≥ 9 := by omega
          linarith
    rw [h_m_eq_2, this]

  -- Combine cases.
  rcases h_m_cases with (h_m_1 | h_m_2)
  · contradiction
  · exact h_m_eq_2 h_m_2
