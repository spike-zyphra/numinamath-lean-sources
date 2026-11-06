import Mathlib
/- Let $K$ be an integer such that $K \equiv 2 \pmod 3$ and $K \equiv 1 \pmod 7$.
Consider the sequence $\{v_n\}_{n \ge 0}$ defined by $v_639495 = 0$, $v_639495 = 1$, and $v_{m+1} = K v_m - v_{m-1}$ for $m \ge 1$.
Prove that for any positive integers $\alpha$ and $\beta$, and for any natural number $n$, the term $v_n$ is not equal to $3^{\alpha} \cdot 5^{\beta}$. -/
theorem algebra_639495 (k : ℤ) (hk1 : k ≡ 2 [ZMOD 3]) (hk2 : k ≡ 1 [ZMOD 7]) (v : ℕ → ℤ) (h1 : v 0 = 0) (h2 : v 1 = 1) (h3 : ∀ m : ℕ, v (m + 2) = k * v (m + 1) - v m) : ∀ a b : ℕ, a > 0 → b > 0 → (∃ n : ℕ, v n = 3 ^ a * 5 ^ b) → False:= by
  -- Pattern for v_n modulo 3: v(3m) ≡ 0, v(3m+1) ≡ 1, v(3m+2) ≡ 2 (mod 3)
  have h4 : ∀ m : ℕ, v (3 * m) ≡ 0 [ZMOD 3] ∧ v (3 * m + 1) ≡ 1 [ZMOD 3] ∧ v (3 * m + 2) ≡ 2 [ZMOD 3]:= by
    intro m
    induction m with
    | zero =>
      simp
      rw [h1, h2]
      refine ⟨rfl, rfl, ?_⟩
      rw [h3 0, h1, h2]
      simp
      exact hk1
    | succ m ih =>
      rcases ih with ⟨-, ih2, ih3⟩
      -- Prove v(3(m+1)) ≡ 0 (mod 3)
      have h4 : v (3 * (m + 1)) ≡ 0 [ZMOD 3]:= by
        rw [show 3 * (m + 1) = 3 * m + 1 + 2 by omega]
        rw [h3 (3 * m + 1)]
        rw [show 3 * m + 1 + 1 = 3 * m + 2 by omega]
        replace hk1 : k * v (3 * m + 2) ≡ 2 * v (3 * m + 2) [ZMOD 3]:= by exact Int.ModEq.mul hk1 rfl
        replace ih3 : 2 * v (3 * m + 2) ≡ 2 * 2 [ZMOD 3]:= by exact Int.ModEq.mul_left 2 ih3
        replace hk1 : k * v (3 * m + 2) ≡ 2 * 2 [ZMOD 3]:= by exact Int.ModEq.trans hk1 ih3
        replace hk1:= Int.ModEq.sub hk1 ih2
        simp at hk1
        exact hk1
      -- Prove v(3(m+1)+1) ≡ 1 (mod 3)
      have h5 : v (3 * (m + 1) + 1) ≡ 1 [ZMOD 3]:= by
        rw [show 3 * (m + 1) + 1 = 3 * m + 2 + 2 by omega]
        rw [h3 (3 * m + 2)]
        rw [show 3 * m + 2 + 1 = 3 * (m + 1) by omega]
        replace h4 : k * v (3 * (m + 1)) ≡ k * 0 [ZMOD 3]:= by exact Int.ModEq.mul_left k h4
        simp at h4
        replace h4:= Int.ModEq.sub h4 ih3
        simp at h4
        exact h4
      refine ⟨h4, h5, ?_⟩
      -- Prove v(3(m+1)+2) ≡ 2 (mod 3)
      rw [h3 (3 * (m + 1))]
      replace h5 : k * v (3 * (m + 1) + 1) ≡ k * 1 [ZMOD 3]:= by exact Int.ModEq.mul_left k h5
      simp at h5
      replace h5 : k * v (3 * (m + 1) + 1) ≡ 2 [ZMOD 3]:= by exact Int.ModEq.trans h5 hk1
      replace h5:= Int.ModEq.sub h5 h4
      simp at h5
      exact h5
  -- Pattern for v_n modulo 7: 6-periodic pattern starting with 0,1,1,0,-1,-1
  have h5 : ∀ m : ℕ, v (6 * m) ≡ 0 [ZMOD 7] ∧ v (6 * m + 1) ≡ 1 [ZMOD 7] ∧ v (6 * m + 2) ≡ 1 [ZMOD 7] ∧ v (6 * m + 3) ≡ 0 [ZMOD 7] ∧ v (6 * m + 4) ≡ -1 [ZMOD 7] ∧ v (6 * m + 5) ≡ -1 [ZMOD 7]:= by
    -- Simplify recurrence relation modulo 7 using k ≡ 1 (mod 7)
    replace h3 : ∀ m : ℕ, v (m + 2) ≡ v (m + 1) - v m [ZMOD 7]:= by
      intro m
      rw [h3 m]
      replace hk2 : k * v (m + 1) ≡ 1 * v (m + 1) [ZMOD 7]:= by exact Int.ModEq.mul hk2 rfl
      simp at hk2
      exact Int.ModEq.sub hk2 rfl
    intro m
    induction m with
    | zero =>
      simp
      -- Base case: compute first 6 terms modulo 7
      have g1 : v 0 ≡ 0 [ZMOD 7]:= by rw [h1]
      have g2 : v 1 ≡ 1 [ZMOD 7]:= by rw [h2]
      have g3 : v 2 ≡ 1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g2 g1
        exact Int.ModEq.trans (h3 0) g
      have g4 : v 3 ≡ 0 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g3 g2
        exact Int.ModEq.trans (h3 1) g
      have g5 : v 4 ≡ -1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g4 g3
        exact Int.ModEq.trans (h3 2) g
      have g6 : v 5 ≡ -1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g5 g4
        exact Int.ModEq.trans (h3 3) g
      exact ⟨g1, g2, g3, g4, g5, g6⟩
    | succ m ih =>
      rcases ih with ⟨-, -, -, -, ih5, ih6⟩
      rw [show 6 * (m + 1) = 6 * m + 6 by omega]
      -- Inductive step: compute next 6 terms using recurrence
      have g1 : v (6 * m + 6) ≡ 0 [ZMOD 7]:= by
        have g:= Int.ModEq.sub ih6 ih5
        exact Int.ModEq.trans (h3 (6 * m + 4)) g
      have g2 : v (6 * m + 6 + 1) ≡ 1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g1 ih6
        exact Int.ModEq.trans (h3 (6 * m + 5)) g
      have g3 : v (6 * m + 6 + 2) ≡ 1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g2 g1
        exact Int.ModEq.trans (h3 (6 * m + 6)) g
      have g4 : v (6 * m + 6 + 3) ≡ 0 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g3 g2
        exact Int.ModEq.trans (h3 (6 * m + 7)) g
      have g5 : v (6 * m + 6 + 4) ≡ -1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g4 g3
        exact Int.ModEq.trans (h3 (6 * m + 8)) g
      have g6 : v (6 * m + 6 + 5) ≡ -1 [ZMOD 7]:= by
        have g:= Int.ModEq.sub g5 g4
        exact Int.ModEq.trans (h3 (6 * m + 9)) g
      exact ⟨g1, g2, g3, g4, g5, g6⟩
  -- Main proof: assume v_n = 3^a * 5^b and derive contradiction
  intro a b ha _ h
  rcases h with ⟨n, hn⟩
  -- Set A = a - 1 for easier manipulation
  set A:= a - 1 with hA
  clear_value A
  replace hA : a = A + 1:= by omega
  subst a
  clear ha
  ring_nf at hn
  -- Show that 3 divides v_n
  have h : 3 ∣ v n:= by
    rw [hn]
    use 3 ^ A * 5 ^ b
    ring
  -- Show that 7 does not divide v_n (contradiction since 7 divides v_n for certain n)
  replace hn : ¬(7 ∣ v n):= by
    have g : Nat.Prime 7:= by norm_num
    by_contra H
    rw [hn] at H
    replace H : 7 ∣ 3 ^ A * 5 ^ b * 3:= by
      zify
      exact H
    rw [show 3 ^ A * 5 ^ b * 3 = 3 ^ (A + 1) * 5 ^ b by ring_nf] at H
    replace H : 7 ∣ 3 ^ (A + 1) ∨ 7 ∣ 5 ^ b:= by exact (Nat.Prime.dvd_mul g).mp H
    rcases H with H | H
    .
      replace H : 7 ∣ 3:= by exact Nat.Prime.dvd_of_dvd_pow g H
      omega
    .
      replace H : 7 ∣ 5:= by exact Nat.Prime.dvd_of_dvd_pow g H
      omega
  -- Show that 3 divides n (using modulo 3 pattern)
  replace h : 3 ∣ n:= by
    mod_cases n % 3
    .
      exact Nat.dvd_of_mod_eq_zero H
    .
      -- Case n ≡ 1 (mod 3): leads to contradiction 1 ≡ 0 (mod 3)
      have g : n ≥ n % 3:= by exact Nat.mod_le n 3
      rw [H] at g
      simp at g
      replace H : 3 ∣ n - 1:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨m, hm⟩
      replace hm : n = 3 * m + 1:= by omega
      subst n
      replace h : v (3 * m + 1) ≡ 0 [ZMOD 3]:= by exact Dvd.dvd.modEq_zero_int h
      replace h4:= (h4 m).2.1
      replace h : 1 ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h)) h4)
      simp [Int.ModEq] at h
    .
      -- Case n ≡ 2 (mod 3): leads to contradiction 2 ≡ 0 (mod 3)
      have g : n ≥ n % 3:= by exact Nat.mod_le n 3
      rw [H] at g
      simp at g
      replace H : 3 ∣ n - 2:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨m, hm⟩
      replace hm : n = 3 * m + 2:= by omega
      subst n
      replace h : v (3 * m + 2) ≡ 0 [ZMOD 3]:= by exact Dvd.dvd.modEq_zero_int h
      replace h4:= (h4 m).2.2
      replace h : 2 ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h)) h4)
      simp [Int.ModEq] at h
  rcases h with ⟨k, hk⟩
  by_cases g : Odd k
  .
    -- Case k is odd: n = 3(2m+1) = 6m+3, but v(6m+3) ≡ 0 (mod 7)
    rcases g with ⟨m, rfl⟩
    rw [show 3 * (2 * m + 1) = 6 * m + 3 by omega] at hk
    subst n
    replace h5:= (h5 m).2.2.2.1
    replace h6 : 7 ∣ v (6 * m + 3):= by exact Int.dvd_of_emod_eq_zero h5
    trivial
  .
    -- Case k is even: n = 3(2m) = 6m, but v(6m) ≡ 0 (mod 7)
    simp at g
    rcases g with ⟨m, rfl⟩
    rw [show 3 * (m + m) = 6 * m by omega] at hk
    subst n
    replace h5:= (h5 m).1
    replace h5 : 7 ∣ v (6 * m):= by exact Int.dvd_of_emod_eq_zero h5
    trivial
