import Mathlib

/-
The sequence $\left\{a_{n}\right\}_{n \geq 1}$ is defined by
$a_{n+2}=7 a_{n+1}-a_{n}$ for positive integers $n$ with initial values $a_{1}=1$ and $a_{2}=8$.
Another sequence, $\left\{b_{n}\right\}$,
is defined by the rule $b_{n+2}=3 b_{n+1}-b_{n}$ for positive integers $n$
together with the values $b_{1}=1$ and $b_{2}=2$.
Find $\operatorname{gcd}\left(a_{5000}, b_{501}\right)$.
-/
theorem number_theory_608208 {a b: PNat → ℕ}
  (ha: ∀n, a (n+2) = 7 * a (n+1) - a n)
  (ha1: a 1 = 1) (ha2: a 2 = 8)
  (hb: ∀n, b (n+2) = 3 * b (n+1) - b n)
  (hb1: b 1 = 1) (hb2: b 2 = 2):
  Nat.gcd (a 5000) (b 501) = 89 := by

  -- positive integer n is either 1,2, or m + 2
  have pn_or (n:PNat): n = 1 ∨ n = 2 ∨ ∃(m:PNat), n = m+2 := by
    by_cases hn1: n = 1
    · simp [hn1]
    rcases (PNat.exists_eq_succ_of_ne_one hn1) with ⟨n, rfl⟩
    by_cases hn2: n = 1
    · right; left
      rw [hn2]
      rfl
    rcases (PNat.exists_eq_succ_of_ne_one hn2) with ⟨n, rfl⟩
    right;right
    use n
    rfl

  -- note that F (k+2) = 3 F(k) - F (k-2)
  have hfib1 (k:ℕ): Nat.fib (k+4) = 3 * Nat.fib (k+2) - (Nat.fib k:ℤ) := by
    have h1: Nat.fib (k+4) = 2 * (Nat.fib (k+2)) + Nat.fib (k+1) := by
      nth_rw 1 [Nat.fib_add_two]
      have: Nat.fib (k+2+1) = Nat.fib (k+1) + Nat.fib (k+2) := by
        rw [← Nat.fib_add_two]
      rw [this]
      ring
    have h2: Nat.fib (k+1) = Nat.fib (k+2) - Nat.fib k := by
      simp [Nat.fib_add_two]
    rw [h1, h2]
    push_cast
    rw [Nat.cast_sub (le_trans
    (Nat.fib_le_fib_succ) (Nat.fib_le_fib_succ))]
    ring
  -- also, F (k+4) = 7 F (k) - F (k-4)
  have hfib2 (k:ℕ): Nat.fib (k+8) = 7 * Nat.fib (k+4) - (Nat.fib k:ℤ) := by
    have h1: k+8 = k+4 + 4 := by ring
    have h2: k+4+2 = k+2 + 4 := by ring
    rw [h1, hfib1 (k+4), h2, hfib1 (k+2)]
    ring_nf
    rw [add_comm 4 k, hfib1 k]
    ring_nf
  -- and F3 = 2, F6 = 8.
  have fib_3_eq: Nat.fib 3 = 2 := by
    simp [Nat.fib_add_two]
  have fib_6_eq: Nat.fib 6 = 8 := by
    simp [Nat.fib_add_two]

  -- therefore, use induction, we can give general formula of a and b.

  -- a n =  F (4n-2), F is the fibonacci sequence
  have ha: ∀n, a n = Nat.fib (4*n-2) := by
    intro n
    induction' n using PNat.strongInductionOn with n ih
    rcases (pn_or n) with (rfl | rfl | ⟨m, rfl⟩)
    · simp [ha1]
    · simp [ha2, fib_6_eq]
    · rw [ha m, ih (m+1) (by simp), ih m (PNat.lt_add_right m 2)]
      zify
      have mge: m ≥ (1:ℕ) := NeZero.one_le
      have h1: 4*(m+1)-(2:ℕ) = (4*m-2) + 4 := by omega
      have h2: 4*(m+2:ℕ) - 2 = (4*m-2) + 8 := by omega
      rw [h1, h2, Nat.cast_sub, hfib2]
      norm_cast
      have: 4*m-2 ≤ 4*m-2 + (4:ℕ) := by simp
      linarith only [Nat.fib_mono this]

  -- b n = F (2n-1)
  have hb: ∀n, b n = Nat.fib (2*n-1) := by
    intro n
    induction' n using PNat.strongInductionOn with n ih
    rcases (pn_or n) with (rfl | rfl | ⟨m, rfl⟩)
    · simp [hb1]
    · simp [hb2, fib_3_eq]
    · rw [hb m, ih (m+1) (by simp), ih m (PNat.lt_add_right m 2)]
      zify
      have mge: m ≥ (1:ℕ) := NeZero.one_le
      have h1: 2*(m+1:ℕ)-1 = (2*m-1) + 2 := by omega
      have h2: 2*(m+2:ℕ)-1 = (2*m-1) + 4 := by omega
      rw [h1, h2, Nat.cast_sub, hfib1]
      norm_cast
      have: 2*m-1 ≤ 2*m-1 + (2:ℕ) := by simp
      linarith only [Nat.fib_mono this]

  -- then a5000 = F19998 = F (11*1818), b501 = F1001 = F (11x91)
  replace ha: a 5000 = Nat.fib (11*1818) := by
    rw [ha]
    norm_num
  replace hb: b 501 = Nat.fib (11*91) := by
    rw [hb]
    norm_num
  -- and notice that we have gcd (Fm, Fn) = F (gcd (m,n))
  rw [ha, hb, ← Nat.fib_gcd]
  -- gcd of 11x1818 and 11x91 is 11, since 1818 and 91 are coprime
  have h1: Nat.gcd (11*1818) (11*91) = 11 := by norm_num
  -- then final answer = F (11) = 89.
  have h2: Nat.fib 11 = 89 := by
    simp [Nat.fib_add_two]
  rw [h1, h2]