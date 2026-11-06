import Mathlib

/- Soit $m$ et $n$ deux entiers naturels. Démontrer que $n!\neq m^{2}+2019$. -/
theorem number_theory_605706 (m n : ℕ) : Nat.factorial n ≠ m^2 + 2019 := by
  -- Let's proceed by contradiction and assume that we have two natural integers $m$ and $n$ such that $n!=m^{2}+2019$.
  intro h_eq
  have h_assume : Nat.factorial n = m ^ 2 + 2019 := h_eq
  -- First, we know that $n!\geqslant 2019&gt;6!=720$, so $n \geqslant 7$.
  have h_n_ge_7 : n ≥ 7 := by
    by_contra h_n_not_ge_7
    have h_n_lt_7 : n < 7 := Nat.not_le.mp h_n_not_ge_7
    have h_n_le_6 : n ≤ 6 := Nat.le_of_lt_succ h_n_lt_7
    have h_fact_le_720 : Nat.factorial n ≤ Nat.factorial 6 := Nat.factorial_le h_n_le_6
    have h_fact_6 : Nat.factorial 6 = 720 := rfl
    have h_fact_n : Nat.factorial n ≤ 720 := by rw [h_fact_6] at h_fact_le_720; exact h_fact_le_720
    have h_m2_2019 : m ^ 2 + 2019 ≥ 2019 := by apply Nat.le_add_left
    have h_720_le_2019 : 720 <  2019 := by norm_num
    have h_contr : Nat.factorial n < m ^ 2 + 2019 := by
      linarith [h_fact_n, h_m2_2019, h_720_le_2019]
    rw [h_assume] at h_contr
    exact Nat.lt_irrefl _ h_contr
  -- $n!$ is divisible by $7!=2^{4} \times 3^{2} \times 5 \times 7$, and we have $0 \equiv m^{2}+2019$ $(\bmod 7!)$.
  have h_mod_7fact : Nat.factorial n ≡ 0 [MOD Nat.factorial 7] := by
    exact Nat.modEq_zero_iff_dvd.mpr (Nat.factorial_dvd_factorial h_n_ge_7)
  -- $7! = 2^4 * 3^2 * 5 * 7$, check modulo $9 = 3^2$, need $m^2 + 2019 ≡ 0 (mod 9)$.
  have h_mod_9 : m ^ 2 + 2019 ≡ 0 [MOD 9] := by
    have h_7fact : Nat.factorial 7 = 5040 := rfl
    have h_9_dvd_7fact : 9 ∣ Nat.factorial 7 := by
      have : Nat.factorial 7 = 7 * 6 * 5 * 4 * 3 * 2 * 1 := rfl
      have : 9 = 3 * 3 := rfl
      apply Nat.dvd_of_mod_eq_zero
      norm_num[Nat.factorial_succ, Nat.mul_mod, Nat.mod_eq_of_lt]
    have h_nfact_mod_9 : Nat.factorial n ≡ 0 [MOD 9] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      exact Nat.dvd_trans h_9_dvd_7fact (Nat.modEq_zero_iff_dvd.mp h_mod_7fact)
    rw [← h_assume]
    exact h_nfact_mod_9
  -- Compute $2019$ mod $9$.
  have h_2019_mod_9 : 2019 ≡ 3 [MOD 9] := by
    rw [Nat.modEq_iff_dvd]
    norm_num
  -- If $m^2 ≡ 6 (mod 9)$, then $3 ∣ m,$ so $m^2 ≡ 0 (mod 9)$, contradiction.
  have h_contr_m2 : ¬ (m ^ 2 ≡ 6 [MOD 9]) := by
    intro h_m2_six
    have h_m_div_3 : 3 ∣ m := by
      apply Nat.dvd_of_mod_eq_zero
      by_contra h_m_not_div_3
      have h_m_mod_3 : m % 3 = 1 ∨ m % 3 = 2 := by
        have h_mod : m % 3 < 3 := Nat.mod_lt m (by decide)
        have h_cases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
          have h : m % 3 < 3 := h_mod
          match h' : m % 3 with
          | 0 => exact Or.inl rfl
          | 1 => exact Or.inr (Or.inl rfl)
          | 2 => exact Or.inr (Or.inr rfl)
          | n + 3 =>  have h_eq : n + 3 = n.succ.succ.succ := by simp [Nat.succ]
                      have h_ge : n + 3 ≥ 3 := Nat.le_add_left 3 n
                      have h_lt : n + 3 < 3 := by rw [h_eq,← h']; exact h
                      exact absurd h_ge (Nat.not_le_of_gt h_lt)
        rcases h_cases with h_zero | h_one | h_two
        · have h_div : 3 ∣ m := Nat.dvd_of_mod_eq_zero h_zero
          contradiction
        · exact Or.inl h_one
        · exact Or.inr h_two
      have h_m2_mod_3 : m ^ 2 % 3 = 1 := by
        cases h_m_mod_3
        case inl h_m_1 =>
          have : m % 3 = 1 := h_m_1
          calc
            m ^ 2 % 3 = (m % 3) ^ 2 % 3 := by rw [Nat.pow_mod]
            _ = 1 ^ 2 % 3 := by rw [this]
            _ = 1 % 3 := by norm_num
            _ = 1 := by norm_num
        case inr h_m_2 =>
          have : m % 3 = 2 := h_m_2
          calc
            m ^ 2 % 3 = (m % 3) ^ 2 % 3 := by rw [Nat.pow_mod]
            _ = 2 ^ 2 % 3 := by rw [this]
            _ = 4 % 3 := by norm_num
            _ = 1 := by norm_num
      -- Derive $m^2 mod 3$ from $m^2 ≡ 6 (mod 9)$.
      have h_m2_mod_3_from_9 : m ^ 2 % 3 = 0 := by
        have h_mod_9: m ^ 2 % 9 = 6 := Nat.mod_eq_of_modEq h_m2_six (by norm_num : 6 < 9)
        calc
          m ^ 2 % 3 = (m ^ 2 % 9) % 3 := by symm; apply Nat.mod_mod_of_dvd; norm_num
          _ = 6 % 3 := by rw [h_mod_9]
          _ = 0 := by norm_num
      rw [h_m2_mod_3_from_9] at h_m2_mod_3
      norm_num at h_m2_mod_3
    -- Use $3 ∣ m$ to show $m^2 ≡ 0 (mod 9)$.
    have h_m2_div_9 : 9 ∣ m ^ 2 := by
      exact pow_dvd_pow_of_dvd h_m_div_3 2
    have h_m2_mod_9_zero : m ^ 2 ≡ 0 [MOD 9] := Nat.modEq_zero_iff_dvd.mpr h_m2_div_9
    -- Contradiction: $0 ≡ 6 (mod 9)$ is impossible.
    have h_zero_eq_six : 0 ≡ 6 [MOD 9] := Nat.ModEq.trans (Nat.ModEq.symm h_m2_mod_9_zero) (h_m2_six)
    have h_false : ¬ 0 ≡ 6 [MOD 9] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    exact h_false h_zero_eq_six
  -- Combine the contradiction modulo $9$.
  have h_m2_2019_mod_9 : m ^ 2 + 2019 ≡ m ^ 2 + 3 [MOD 9] := by
    exact Nat.ModEq.add (Nat.ModEq.refl (m ^ 2)) h_2019_mod_9
  have h_final_contr : m ^ 2 + 2019 ≡ 0 [MOD 9] ∧ m ^ 2 + 2019 ≡ m ^ 2 + 3 [MOD 9] := by
    exact ⟨h_mod_9, h_m2_2019_mod_9⟩
  -- Derive $m^2 ≡ 6 (mod 9)$ from the combined congruences.
  have h_m2_eq_six : m ^ 2 ≡ 6 [MOD 9] := by
    have h_m2_plus_3_eq_zero : m ^ 2 + 3 ≡ 0 [MOD 9] := Nat.ModEq.trans (Nat.ModEq.symm h_m2_2019_mod_9) h_mod_9
    have h_m2_plus_9_eq_6 : m ^ 2 + 9 ≡ 6 [MOD 9] := by
      have : m ^ 2 + 9 = m ^ 2 + 3 + 6 := by ring
      rw [this]
      exact Nat.ModEq.add h_m2_plus_3_eq_zero (Nat.ModEq.refl 6)
    have h_m2_eq_m2_plus_9 : m ^ 2 ≡ m ^ 2 + 9 [MOD 9] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    exact Nat.ModEq.trans h_m2_eq_m2_plus_9 h_m2_plus_9_eq_6
  -- Conclude with the contradiction .
  exact h_contr_m2 h_m2_eq_six
