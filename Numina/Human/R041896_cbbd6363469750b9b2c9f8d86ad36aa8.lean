import Mathlib

open Real

/- Denote by $P(n)$ the greatest prime divisor of $n$. Find all integers $n \geq 2$ for which

$$
P(n)+\lfloor\sqrt{n}\rfloor=P(n+1)+\lfloor\sqrt{n+1}\rfloor .
$$

(Note: $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x$.) -/
/-
Autoformalization is correct but using Real.sqrt after opening Real is too verbose.
theorem number_theory_605721 {P : ℕ → ℕ}
    (hP : ∀ n, P n = sSup {p | p.Prime ∧ p ∣ n}) :
    {n | 2 ≤ n ∧ P n + ⌊Real.sqrt n⌋ = P (n + 1) + ⌊Real.sqrt (n + 1)⌋} = {3} := by sorry
-/
theorem number_theory_605721 {P : ℕ → ℕ}
    (hP : ∀ n, IsGreatest {p | p.Prime ∧ p ∣ n} (P n) ) :
    {n | 2 ≤ n ∧ P n + ⌊√n⌋ = P (n + 1) + ⌊√(n + 1)⌋} = {3} := by

  -- We prove equality of the two sets by showing inclusion in both directions.
  ext n
  constructor
  . -- We first show that if n is in {n | 2 ≤ n ∧ P n + ⌊√n⌋ = P (n + 1) + ⌊√(n + 1)⌋}
    -- then n is in {3}.
    rw [Set.mem_setOf]
    intro hn
    obtain hPn := hP n
    obtain hPn_succ := hP (n + 1)
    simp [IsGreatest, mem_upperBounds] at hPn hPn_succ
    obtain ⟨ ⟨ primePn, dvdPn ⟩, bdPn ⟩ := hPn
    obtain ⟨ ⟨ primePn_succ, dvdPn_succ ⟩, bdPn_succ ⟩ := hPn_succ

    -- We show that P n ≠ P (n + 1) by contradiction.
    -- Suppose that P n = P (n + 1). Thus, P (n + 1) and P n are the same
    -- prime number, say p. Thus, p divides both (n + 1) and n and therefore
    -- p divides their difference, which is 1. But a prime cannot divide 1,
    -- so we have a contradiction.
    have claim0 : P n ≠ P (n + 1) := by
      by_contra h
      rw [← h] at dvdPn_succ
      have : P n ∣ n + 1 - n := by exact Nat.dvd_sub' dvdPn_succ dvdPn
      ring_nf at this
      rw [Nat.add_sub_assoc] at this
      . simp [Nat.sub_self, Nat.Prime.ne_one primePn] at this
      . rfl

    -- Since P n + ⌊√n⌋ = P (n + 1) + ⌊√(n + 1)⌋ and the claim above has
    -- P n ≠ P (n + 1), we must have ⌊√n⌋ ≠ ⌊√(n + 1)⌋.
    have claim1 : ⌊√n⌋ ≠ ⌊√(n + 1)⌋ := by
      by_contra h
      apply claim0
      obtain ⟨ _, hnr ⟩ := hn
      rw [h] at hnr
      simp at hnr
      exact hnr

    -- We show that ⌊√n⌋ + 1 = ⌊√(n + 1)⌋.
    have claim2 : ⌊√n⌋ + 1 = ⌊√(n + 1)⌋ := by
      -- We first show that for any natural number n that can be written as n = p * p + q
      -- where p and q are in ℕ and q ≤ p + p, then ⌊√n⌋ = p.
      have claim2' {p q n : ℕ} (h : q ≤ p + p) (hn : n = p * p + q): ⌊√n⌋ = p := by
        have le : ⌊√n⌋ ≤ p := by
          suffices ⌊√n⌋ < p + 1 by exact (Int.add_le_add_iff_right 1).mp this
          have : p + 1 = ⌊(p : ℤ) + 1⌋ := by exact rfl
          rw [this]
          have (a :ℝ) (b : ℤ) (hab : a < b) : ⌊a⌋ < ⌊b⌋ := by
            rify
            rw [← Int.floor_le_sub_one_iff]
            simp
            exact hab
          apply this
          rw [Real.sqrt_lt]
          . norm_cast
            calc
              _ ≤ p * p + (p + p) := by rw [hn]; apply Nat.add_le_add_left h
              _ < p * p + (p + p) + 1 := by apply lt_add_one
              _ = _ := by ring
          . norm_cast; omega
          . norm_cast; omega
        have ge : ⌊√n⌋ ≥ p := by
          calc
            _ ≥ ⌊√(p * p)⌋ := by apply Int.floor_le_floor
                                 apply Real.sqrt_le_sqrt
                                 norm_cast
                                 linarith
            _ = ⌊(p : ℤ)⌋ := by rw [Real.sqrt_mul_self_eq_abs]; simp
            _ = _ := by norm_cast
        exact Eq.symm (Int.le_antisymm ge le)

      -- We then show that n can in fact be written as a * a + b where
      -- a and b are in ℕ and b ≤ a + a.
      have c1 : ∃ a b : ℕ, b ≤ a + a ∧ n = a * a + b := by
        use n.sqrt
        use (n - (n.sqrt * n.sqrt))
        constructor
        . by_contra g
          apply claim1
          simp at g
          have : n.sqrt + n.sqrt + n.sqrt * n.sqrt + 1 ≤ n := by exact g
          have : (n.sqrt + 1) ^ 2 ≤ n := by ring_nf at this ⊢; exact this
          have nsq : n = (√n)^2 := by refine Eq.symm (Real.sq_sqrt ?_); exact Nat.cast_nonneg' n
          rify at this
          rw [nsq] at this
          rw [sq_le_sq] at this
          rw [abs_of_nonneg] at this
          . rw [abs_of_nonneg] at this
            . have : ⌊ (n.sqrt + 1 : ℝ) ⌋ ≤ ⌊ √↑n ⌋ := by exact Int.floor_le_floor this
              simp at this
            . apply Real.sqrt_nonneg
          . norm_cast; linarith
        . ring_nf
          rw [← Nat.add_sub_assoc]
          . rw [Nat.add_sub_cancel_left]
          . rw [Nat.pow_two]; exact Nat.sqrt_le n

      obtain ⟨ a, ⟨ b, ⟨ h', h''⟩ ⟩ ⟩ := c1
      norm_cast
      -- Then n + 1 = a * a + (b + 1).
      have : n + 1 = a * a + (b + 1) := by omega
      obtain g := claim2' h' h''
      rw [g]
      by_cases hb : b + 1 ≤ a + a
      . obtain g' := claim2' hb this
        rw [← g] at g'
        norm_cast at claim1 g'
        rw [g'] at claim1
        contradiction
      . have e : b = a + a := by omega
        rw [e] at this
        have nsuccsq : n + 1 = (a + 1)^2 := by ring_nf at *; exact this
        rw [nsuccsq]
        simp
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_pos]
        simp
        linarith

    -- It follows that P n = P (n + 1) + 1.
    have claim3 : P n = P (n + 1) + 1 := by omega

    -- We show that P n = 3 and P (n + 1) = 2.
    have claim4 : P n = 3 ∧ P (n + 1) = 2 := by
      -- Since P (n + 1) is a prime, it must be at least two.
      have : P (n + 1) ≥ 2 := by
        exact Nat.Prime.two_le primePn_succ
      by_cases h : P (n + 1) = 2
      . -- If P (n + 1), then we are done.
        omega
      . -- Otherwise, P (n + 1) ≥ 3.
        have : P (n + 1) ≥ 3 := by omega
        -- Hence, P n must be an odd prime since it is greater than P (n + 1) ≥ 3.
        -- But, P (n + 1) is also an odd prime, which contradicts that P (n + 1)
        -- and P n are consecutive natural numbers.
        have oddPn : Odd (P n) := by
          apply Nat.Prime.odd_of_ne_two primePn
          omega
        rw [claim3] at oddPn
        rw [Nat.odd_add_one] at oddPn
        obtain g := Nat.Prime.odd_of_ne_two primePn_succ (by omega)
        trivial

    -- It follows that n + 1 = 2 ^ b for some positive integer b
    -- since n + 1 ≥ 3 and according to the previous claim,
    -- the largest prime factor of n + 1 is 2 and there is no
    -- prime factor less than 2.
    have claim5a : ∃ b, b > 0 ∧ n + 1 = 2 ^ b := by
      have pnsucc2 : ∀ {d : ℕ}, Nat.Prime d → d ∣ (n + 1) → d = 2 := by
        intro d
        simp [IsGreatest, mem_upperBounds] at hP
        obtain hPn := (hP (n + 1)).right d
        rw [claim4.right] at hPn
        intro h1 h2
        obtain dub := hPn h1 h2
        apply Nat.Prime.two_le at h1
        exact Eq.symm (Nat.le_antisymm h1 dub)
      have : n + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      obtain pnsucc2' := Nat.eq_prime_pow_of_unique_prime_dvd this pnsucc2
      use (n+1).primeFactorsList.length
      constructor
      . suffices ¬(n + 1).primeFactorsList = [] by exact List.length_pos.mpr this
        rw [Nat.primeFactorsList_eq_nil]
        omega
      . trivial

    -- We must have that n = 3 ^ a for some integer a
    -- since according to a claim4, the largest prime factor of n is 3,
    -- n must be odd since n = 2 ^ b with b positive is even,
    -- and there is no odd prime factor less than 3.
    have claim5b : ∃ a : ℕ, n = 3 ^ a := by
      have pn3 : ∀ {d : ℕ}, Nat.Prime d → d ∣ n → d = 3 := by
        intro d
        simp [IsGreatest, mem_upperBounds] at hP
        have : Odd n := by
          suffices Even (n + 1) by rw [← Nat.not_even_iff_odd]
                                   rw [Nat.even_add_one] at this
                                   exact this
          obtain ⟨ b, hb ⟩ := claim5a
          rw [hb.right]
          have : ∃ r, b = r + 1 := by refine Nat.exists_eq_add_one.mpr ?_; exact hb.left
          obtain ⟨ r, hr ⟩ := this
          rw [hr, pow_add, pow_one]
          simp
        obtain hPn := (hP n).right d
        intro h1 h2
        obtain dub := hPn h1 h2
        rw [claim4.left] at hPn dub
        apply Nat.Prime.two_le at h1
        by_cases hd : d = 2
        . rw [hd] at h2
          rw [← even_iff_two_dvd] at h2
          rw [← Nat.not_even_iff_odd] at this
          trivial
        . omega

      have : n ≠ 0 := by omega
      obtain pn3' := Nat.eq_prime_pow_of_unique_prime_dvd this pn3
      use n.primeFactorsList.length

    obtain ⟨ a, hacb ⟩ := claim5b
    obtain ⟨ b, haca ⟩ := claim5a

    -- We can write b as = 2 * c for some positive integer c
    -- since 3 ^ a = 2 ^ b - 1 and if b = 2 * k + 1 for some
    -- nonnegative integer k, we will have
    -- 0 ≡ 2 ^ b - 1 ≡ 2 ^ (2 * k + 1) -1 ≡ 4 ^ k * 2 ≡ 1 * 2 ≡ 2 [ZMOD 3],
    -- which is impossible.
    have : ∃ c : ℕ, c > 0 ∧ b = 2 * c := by
      have : 3 ^ a + 1 = 2 ^ b := by omega
      have ha : ∃ r, a = r + 1 := by suffices a > 0 by exact Nat.exists_eq_add_one.mpr this
                                     by_contra hazero
                                     have : a = 0 := by exact Nat.eq_zero_of_not_pos hazero
                                     rw [this] at hacb
                                     omega
      have : 3 ^ a = 2 ^ b - (1 : ℤ):= by
        zify at this
        rw [← this]
        simp
      obtain ⟨ r, hr ⟩ := ha
      rw [hr, pow_add, pow_one] at this
      have : ↑3 ∣ ↑2 ^ b - (1 : ℤ) := by exact Dvd.intro_left (3 ^ r) this
      by_cases hbEven : Even b
      . obtain ⟨ c, hc ⟩ := hbEven
        use c
        omega
      . simp at hbEven
        apply Int.modEq_of_dvd at this
        obtain ⟨ r, hr ⟩ := hbEven
        rw [hr] at this
        rw [pow_add, pow_one, pow_mul] at this
        simp at this
        have hr2 : 4 ^ r * 2 ≡ 2 [ZMOD 3] := by
          have t : 4 ≡ 1 [ZMOD 3] := by decide
          have : 4^r  ≡ 1^r [ZMOD 3] := by exact Int.ModEq.pow r t
          rw [one_pow] at this
          calc
            _ ≡ 1 * 2 [ZMOD 3] := by exact Int.ModEq.mul this rfl
            _ = 2 := by rw [one_mul]
        have : 1 ≡ 2 [ZMOD 3] := by exact Int.ModEq.trans this hr2
        apply Int.ModEq.dvd at this
        simp at this
        norm_cast at this

    obtain ⟨ c, hc ⟩ := this
    rw [hc.right] at haca

    -- We show that a is indeed positive and so a = m + 1
    -- for some m ∈ ℕ. This follows from that 2 ≤ n = 3 ^ a.
    have claim6 : ∃ m : ℕ, a = m + 1 := by
      have : a ≥ 1 := by by_contra ha
                         simp at ha
                         simp [ha] at hacb
                         omega
      exact Nat.exists_eq_add_one.mpr this

    obtain ⟨ m, hm ⟩ := claim6

    -- We can then factor 3 ^ (m + 1) as (2 ^ c - 1) * (2 ^ c + 1).
    have claim7 : 3 ^ (m + 1) = (2 ^ c - 1) * (2 ^ c + 1) := by
      have : (2 ^ c - 1) * (2 ^ c + 1) = 2 ^ (2 * c) - 1 := by
        rw [mul_comm, ← Nat.sq_sub_sq, ← pow_mul]
        ring_nf
      rw [this]
      rw [hm] at hacb
      -- obtain ⟨ hn1, hn2 ⟩ := hacb
      rw [hacb] at haca
      exact Nat.eq_sub_of_add_eq haca.right

    -- We claim that 2 ^ c - 1 = 1.
    have claim8 : 2 ^ c - 1 = 1 := by
      -- We divide into two cases: First is when 3 divides 2 ^ c - 1 and the second otherwise.
      by_cases h3 : 3 ∣ 2 ^ c - 1
      . -- Case 1: 3 divides 2 ^ c - 1. We subdivide into two cases.
        by_cases h3' : 3 ∣ 2 ^ c + 1
        . -- Subcase a: 3 divides 2 ^ c + 1.
          -- Then 3 divides 2 ^ c - 1 + (2 ^ c + 1) = 2 ^ (c + 1),
          -- which is impossible since 3 does not divide a power of 2.
          have : 3 ∣ 2 ^ (c + 1) := by
            have : 2 ^ (c + 1) = 2 ^ c - 1 + (2 ^ c + 1) := by
              ring_nf
              rw [← Nat.add_sub_assoc]
              . nth_rewrite 2 [add_comm]
                rw [Nat.add_sub_assoc]
                . rw [Nat.sub_self]
                  simp
                  ring
                . norm_num
              . exact Nat.one_le_two_pow
            rw [this]
            exact (Nat.dvd_add_iff_right h3).mp h3'
          apply Nat.Prime.dvd_of_dvd_pow at this
          . norm_num at this
          . exact Nat.prime_three
        . -- Subcase b: 3 does not divide 2 ^ c + 1.
          -- Clearly, 2 ^ c + 1 divides 3 ^ (m + 1).
          have : 2 ^ c + 1 ∣ 3 ^ (m + 1) := by exact Dvd.intro_left (2 ^ c - 1) (id (Eq.symm claim7))
          -- Then, 2 ^ c + 1 = 3 ^ k for some k ∈ ℕ.
          rw [Nat.dvd_prime_pow] at this
          obtain ⟨ k, ⟨ hkl, hkr ⟩  ⟩ := this
          rw [hkr] at h3'

          by_cases g : k = 0
          . -- It is easily seen that k cannot be 0.
            rw [g] at hkr
            simp at hkr
          . -- So, k = r + 1 for some r ∈ ℕ.
            have : ∃ r, k = r + 1 := by exact Nat.exists_eq_succ_of_ne_zero g
            obtain ⟨ r, hr ⟩ := this
            rw [hr] at h3'
            -- But this means that 3 ∣ 2 ^ c + 1, a contradiction.
            by_contra
            apply h3'
            rw [pow_add]
            norm_num
          exact Nat.prime_three

      . -- Case 2: 3 does not divide 2 ^ c - 1.
        -- We claim that 2 ^ c - 1 divides 3.
        have : 2 ^ c - 1 ∣ 3 := by
          -- It suffices to show that 2 ^ c - 1 divides 3 ^ (m + 1) since
          -- if this is so, 2 ^ c - 1  = 3 ^ k for some k ∈ ℕ.
          suffices 2 ^ c - 1 ∣ 3 ^ (m + 1) by
            rw [Nat.dvd_prime_pow] at this
            obtain ⟨ k, ⟨ hkl, hkr ⟩  ⟩ := this
            rw [hkr] at h3
            by_cases g : k = 0
            . -- It is easily seen that k cannot be 0.
              rw [g] at hkr
              simp at hkr
              rw [hkr]
              decide
            . -- So, k = r + 1 for some r ∈ ℕ.
              have : ∃ r, k = r + 1 := by exact Nat.exists_eq_succ_of_ne_zero g
              obtain ⟨ r, hr ⟩ := this
              rw [hr] at h3
              -- But this means that 3 ∣ 2 ^ c - 1, a contradiction.
              by_contra
              apply h3
              rw [pow_add]
              norm_num
            exact Nat.prime_three
          -- Now, by claim7, 2 ^ c - 1 is a factor of 3 ^ (m + 1) and so
          -- 2 ^ c - 1 divides 3 ^ (m + 1).
          exact Dvd.intro (2 ^ c + 1) (id (Eq.symm claim7))
        rw [Nat.dvd_prime] at this
        . omega
        . exact Nat.prime_three

    -- It follows that n = 3.
    have claim9 : n = 3 := by
      -- Indeed, c = 1 because by claim8, 2 ^ c - 1 = 1 implies that c = 1.
      have : c = 1 := by
        have : 2 ^ c = 2 ^ 1 := by exact Nat.pred_eq_succ_iff.mp claim8
        rw [pow_right_inj₀] at this
        exact this
        repeat norm_num
      -- So, n + 1 = 2 ^ (2 * c), thus giving n + 1 = 4 which reduces to n = 3.
      rw [this] at haca
      simp at haca
      exact haca

    simp [claim9]

  . simp
    -- We check that if n = 3, then n satisfies
    -- 2 ≤ n and (P n) + ⌊√n⌋ = (P (n + 1)) + ⌊√(n + 1)⌋.
    intro hx
    rw [hx]
    constructor
    . -- 2 ≤ 3 is obvious
      norm_num
    . simp [hP]
      -- When n = 3, we can compute that
      -- and that ⌊√n⌋ = ⌊√3⌋ = 1.
      norm_num
      -- Also, ⌊√(n + 1)⌋ = ⌊√4⌋ = 2
      have : √4 = 2 := by
        calc
          _ = √(2 ^ 2) := by norm_num
          _ = _ := by apply sqrt_sq; norm_num
      rw [this]
      clear this
      norm_num
      norm_cast
      -- Hence, we need to check that (P 3) + 1 = (P 4) + 2.
      -- Note that P n = 3
      have t1 : P 3 = 3 := by
        obtain h3 := hP 3
        simp [IsGreatest, mem_upperBounds] at h3
        obtain ⟨ ⟨ hl, hr ⟩, _ ⟩ := h3
        rwa [Nat.prime_dvd_prime_iff_eq hl Nat.prime_three] at hr
      -- Note that P 4 = 2
      have t2 : P 4 = 2 := by
        obtain h4 := hP 4
        simp [IsGreatest, mem_upperBounds] at h4
        obtain ⟨ ⟨ hl, hr ⟩, _ ⟩ := h4
        have : 4 = 2 ^ 2 := by rfl
        nth_rewrite 2 [this] at hr
        apply Nat.prime_eq_prime_of_dvd_pow hl Nat.prime_two
        exact hr

      -- The result follows.
      rw [t1, t2]