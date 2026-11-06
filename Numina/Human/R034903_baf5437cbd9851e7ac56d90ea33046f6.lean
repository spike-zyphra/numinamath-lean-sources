import Mathlib

/- 8.12 Two integer sequences $\left\{a_{k}\right\}_{k \geqslant 0}$ and $\left\{b_{k}\right\}_{k \geqslant 0}$ satisfy

$$

\begin{array}{l}
b_{k}=a_{k}+9, \\
a_{k+1}=8 b_{k}+8, \quad(k \geqslant 0) .
\end{array}

$$


Furthermore, the number 1988 appears in $\left\{a_{k}\right\}_{k \geqslant 0}$ or $\left\{b_{k}\right\}_{k \geqslant 0}$.
Prove that the sequence $\left\{a_{k}\right\}_{k \geqslant 0}$ does not contain any perfect square terms.
(Austrian-Polish Mathematical Competition, 1988) -/
theorem number_theory_219967 {a b : ℕ → ℤ}
    (h₀ : ∀ k, b k = a k + 9)
    (h₁ : ∀ k, a (k + 1) = 8 * b k + 8)
    (h₂ : ∃ k, a k = 1988 ∨ b k = 1988) :
    ¬∃ n, ∃ m, a m = n ^ 2 := by
  -- Suppose a_m = n^2
  intro ⟨n, m, h_nm⟩
  -- From the given condition, we have a_{k + 1} = 8 a_k + 80
  have a_recurrence (k: ℕ): a (k + 1) = 8 * a k + 80 := by
    rw [h₁, h₀]
    ring
  -- When k ≥ 3, this implies a_k = 8 * (8 * (8 * a_{k - 3} + 80) + 80) + 80 = 16 (32 a_{k - 3} + 365)
  -- Considering mod 8, we have 32 a_{k - 3} + 365 ≡ 5 (mod 8), which will imply that it is not a square
  have a_mod_8 {n: ℕ} (h: n ≥ 3): ∃ m, a n = 16 * (8 * m + 5) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, add_comm]
    repeat rw [a_recurrence]
    use 4 * a k + 45
    ring
  -- We show that if 16x is a square, then x is a square
  have h_sq_of_16_mul {m n: ℤ} (h: n^2 = 16 * m): ∃ k: ℕ, m = k^2 := by
    have h_div: 4^2 ∣ n^2 := Dvd.intro m (id (Eq.symm h))
    replace h_div := (Int.pow_dvd_pow_iff (by norm_num)).mp h_div
    obtain ⟨k, h_k⟩ := h_div
    use k.natAbs
    zify
    rw [h_k] at h
    ring_nf at h
    rw [← sq_abs] at h
    omega
  -- Squares are not 5 modulo 8
  have h_sq_mod_8 {m: ℕ}: m^2 % 8 ≠ 5 := by
    have h: m^2 % 8 = (m % 8)^2 % 8 := by simp [Nat.pow_mod, Nat.add_mod]
    have: m % 8 < 8 := Nat.mod_lt m (show 8 > 0 from by norm_num)
    interval_cases hm: (m % 8)
    all_goals rw [h]; norm_num
  -- If m ≥ 3, then we have seen that a_m = 16(8s + 5) for some s. But 8s + 5 is not a square, so in this case a_m is not a square
  by_cases h_m3: m ≥ 3
  obtain ⟨s, hs⟩ := a_mod_8 h_m3
  rw [h_nm] at hs
  obtain ⟨t, ht⟩ := h_sq_of_16_mul hs
  lift s to ℕ using by nlinarith
  norm_cast at ht
  replace ht: t^2 % 8 = 5 := by omega
  exact h_sq_mod_8 ht
  -- Next we verify that a_0, a_1, and a_2 are not perfect squares
  replace h_m3 := lt_of_not_ge h_m3
  -- Since for k ≥ 1, 8 ∣ a_k
  have h_a_multiple_of_8 (n: ℕ) (h: n ≥ 1): a n % 8 = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, add_comm, a_recurrence]
    omega
  -- and b_k is odd
  have h_b_odd (n: ℕ) (h: n ≥ 1): b n % 2 = 1 := by
    rw [h₀]
    have := h_a_multiple_of_8 n h
    omega
  -- therefore a_k and b_k are both not equal to 1988
  obtain ⟨k, hk⟩ := h₂
  -- Thus it must be that a_0 = 1988 or b_0 = 1988. When b_0 = 1988, a_0 = 1979
  have h_a_zero: a 0 = 1988 ∨ a 0 = 1979 := by
    rcases hk with ha | hb
    -- If k ≥ 1, then a_k is a multiple of 8, hence not equal to 1988
    by_cases hk: k ≥ 1
    have := h_a_multiple_of_8 k hk
    omega
    -- So if some a_k = 1988, then it must be a_0
    rw [show k = 0 from by linarith] at ha
    exact Or.inl ha
    -- If k ≥ 1, then b_k is odd, and hence is not equal to 1988
    by_cases hk: k ≥ 1
    have := h_b_odd k hk
    omega
    -- So if some b_k = 1988, then it must be b_0
    rw [show k = 0 from by linarith, h₀] at hb
    right; omega
  interval_cases m
  -- We show that a_0 is not a square. We have that a_0 = 1988 or 1979, and both lie strictly between 44^2 and 45^2
  rcases h_a_zero with h | h <;> {
    rw [h_nm] at h
    have := sq_lt_sq.mp (show 44^2 < n^2 from by linarith)
    norm_num at this
    have := sq_lt_sq.mp (show n^2 < 45^2 from by linarith)
    norm_num at this
    linarith
  }
  -- We show that a_1 is not a square. We have that a_1 8 * 1988 or 8 * 1989, and both lie strictly between 126^2 and 127^2
  rcases h_a_zero with h | h <;> {
    rw [a_recurrence, h] at h_nm
    have := sq_lt_sq.mp (show 126^2 < n^2 from by linarith)
    norm_num at this
    have := sq_lt_sq.mp (show n^2 < 127^2 from by linarith)
    norm_num at this
    linarith
  }
  -- We show that a_2 is not a square.
  -- We could bound a_2 between two squares like in the other cases, but instead
  -- we note that a_2 is divisible by 16, and show that a_2/16 is not a square
  rcases h_a_zero with h | h
  -- If a_0 = 1988, then a_1 = 8 * 1998
  replace h: a 1 = 8 * 1998 := by rw [a_recurrence, h]; norm_num
  -- And a_2 = 8 * (8 * 1998) + 80 = 16(4 * 1998 + 5).
  replace h: a 2 = 16 * (8 * 999 + 5) := by rw [a_recurrence, h]; norm_num
  rw [h_nm] at h
  obtain ⟨n, h⟩ := h_sq_of_16_mul h
  norm_cast at h
  -- Since 4 * 1998 + 5 = 8 * 999 + 5 ≡ 5 (mod 8), it is not a square
  replace h: n^2 % 8 = 5 := by omega
  exact h_sq_mod_8 h
  -- If a_0 = 1979, then a_1 = 8 * 1989
  replace h: a 1 = 8 * 1989 := by rw [a_recurrence, h]; norm_num
  -- And a_2 = 8(8 * 1989 + 10) = 16 * 7961
  replace h: a 2 = 16 * 7961 := by rw [a_recurrence, h]; norm_num
  rw [h_nm] at h
  obtain ⟨n, hn⟩ := h_sq_of_16_mul h
  norm_cast at hn
  -- Since 7961 ≡ 2 (mod 3), it is not a square
  have h: n^2 % 3 = (n % 3)^2 % 3 := by simp [Nat.pow_mod, Nat.add_mod]
  have: n % 3 < 3 := Nat.mod_lt n (show 3 > 0 from by norm_num)
  interval_cases hn_mod_3: (n % 3)
  all_goals rw [← hn] at h ; norm_num at h