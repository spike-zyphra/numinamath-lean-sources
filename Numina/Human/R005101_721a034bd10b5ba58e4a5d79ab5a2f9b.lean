import Mathlib

/- Bestimmen Sie alle ganzen Zahlen $n \geq 1$, für die es ein Paar $(a, b)$ von positiven ganzen Zahlen mit folgenden Eigenschaften gibt:
i) Keine dritte Potenz einer Primzahl teilt $a^{2}+b+3$.
ii) Es gilt $\frac{a b+3 b+8}{a^{2}+b+3}=n$.

Antwort: Die einzige ganze Zahl mit diesen Eigenschaften ist $n=2$. -/
theorem number_theory_605526 (n : ℕ) :
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (¬∃ p : ℕ, p.Prime ∧ p^3 ∣ a^2 + b + 3) ∧ ((a : ℚ) * b + 3 * b + 8) / (a^2 + b + 3) = n) ↔ n = 2 := by

  constructor
  . intro h
    obtain ⟨ a, b, hapos, hbpos, hnop, hn ⟩ := h

    -- Note that $a^2 + b + 3 \geq 5$.
    have h1 : a ^ 2 + b + 3 ≥ 5 := by nlinarith

    -- Hence, there exists a prime $p$ that divides $a ^ 2 + b + 3$.
    have h2 : ∃ p, Nat.Prime p ∧ p ∣ a ^ 2 + b + 3 := by
      use (a ^ 2 + b + 3).minFac
      constructor
      . apply Nat.minFac_prime; omega
      . apply Nat.minFac_dvd

    -- We show that for all prime $p$, if $p$ divides $a ^ 2 + b + 3$,
    -- then $p$ divides $a + 1$.
    have hp : ∀ p, Nat.Prime p → p ∣ a ^ 2 + b + 3 → p ∣ a + 1 := by
      intro p hp hpdvd

      -- Since $p$ divides $a^2 + b + 3$, we have $b \equiv -a^2 -3 \bmod p$.
      have h0 : b ≡ -a^2 - 3 [ZMOD p] := by
        have h1 : (p : ℤ) ∣ (a ^ 2 + b + 3 : ℤ) := by
          exact_mod_cast hpdvd
        have h5 : (p : ℤ) ∣ ((b : ℤ) - (-a^2 - 3 : ℤ)) := by
          have eq1 : (b : ℤ) - (-a^2 - 3 : ℤ) = (a ^ 2 + b + 3 : ℤ) := by
            ring_nf
          rw [eq1]
          exact h1
        exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr h5)

      -- Due to the integrality of $n$, $p$ must also be a factor of $ab+3b+8$.
      have h1 : p ∣ (a * b + 3 * b + 8) := by
        obtain ⟨ m, hm ⟩ := hpdvd
        qify at hm
        rw [hm] at hn
        have : (a * b + 3 * b + 8) = p * (m * n) := by
          rw [← mul_assoc]
          qify
          rw [← hn]
          field_simp
          rw [mul_comm ((p : ℚ) * m)]
          rw [mul_div_cancel_right₀]
          norm_cast
          refine Nat.mul_ne_zero ?_ ?_
          . exact Nat.Prime.ne_zero hp
          . by_contra G
            simp [G] at hm
            revert hm
            simp
            norm_cast
        exact Dvd.intro (m * n) (id (Eq.symm this))

      -- Thus, $0 \equiv ab + 3b + 8 \bmod p$.
      have h2 : 0 ≡ a * b + 3 * b + 8 [ZMOD p] := by
        refine (ZMod.intCast_eq_intCast_iff 0 (↑a * ↑b + 3 * ↑b + 8) p).mp ?_
        norm_cast
        exact Eq.symm ((fun a b => (ZMod.natCast_zmod_eq_zero_iff_dvd a b).mpr) (a * b + 3 * b + 8) p h1)

      -- Since $b \equiv -a^2-3 \bmod p$, we have $ab+3b+8\equiv a(-a^2-3)+3(-a^2-3) \bmod p$.
      have h3 : a * b + 3 * b + 8 ≡ a * (-a^2 - 3) + 3 * (-a^2 - 3) + 8 [ZMOD p] := by
        calc
            a * b + 3 * b + 8 ≡ a * (-a^2 - 3) + 3 * b + 8 [ZMOD p] := by
              refine Int.ModEq.add ?_ rfl
              refine Int.ModEq.add ?_ rfl
              exact Int.ModEq.mul_left (↑a) h0
          _ ≡ a * (-a^2 - 3) + 3 * (-a^2 - 3) + 8 [ZMOD p] := by
              refine Int.ModEq.add ?_ rfl
              refine Int.ModEq.add rfl ?_
              exact Int.ModEq.mul_left 3 h0

      -- Now, $a(-a^2-3)+3(-a^2-3) \equiv -(a+1)^3 \bmod p$.
      have h4 : a * (-a^2 - 3) + 3 * (-a^2 - 3) + 8 ≡ -(a + 1)^3 [ZMOD p] := by ring_nf; simp

      have h5 : 0 ≡ -(a + 1)^3 [ZMOD p] := by
        calc
          0 ≡ a * b + 3 * b + 8 [ZMOD p] := h2
          _ ≡ a*(-a^2-3)+3*(-a^2-3)+8 [ZMOD p] := h3
          _ ≡ -(a+1)^3 [ZMOD p]:= h4

      have h6 : (p : ℤ) ∣ (↑a + 1)^3 - 0 := by
        refine Int.modEq_iff_dvd.mp ?_
        exact Int.neg_modEq_neg.mp h5

      have h7 : (p : ℤ) ∣ ↑a + 1 := by simp at h6; exact Int.Prime.dvd_pow' hp h6

      norm_cast at h7

    -- Because of i), every prime $p$ can occur in $a^{2}+b+3$ at most
    -- twice as often as in $a+1$.
    have claim : (a ^ 2 + b + 3).factorization ≤ 2 • (a + 1).factorization := by
      intro p
      by_cases H : Nat.Prime p
      . push_neg at hnop
        obtain h3 := hnop p H
        by_cases G : p ∣ a ^2 + b + 3
        . obtain h4 := hp p H G
          simp
          calc
              (a ^ 2 + b + 3).factorization p ≤ 2 * 1 := by
                by_contra G
                simp at G
                revert h3
                simp
                refine (Nat.Prime.pow_dvd_iff_le_factorization H ?_).mpr G
                omega
            _ ≤ 2 * (a + 1).factorization p := by
                gcongr
                refine (Nat.Prime.dvd_iff_one_le_factorization H ?_).mp (hp p H G)
                omega
        . have : (a ^ 2 + b + 3).factorization p = 0 := by exact Nat.factorization_eq_zero_of_not_dvd G
          rw [this]
          apply Nat.zero_le
      . have : (a ^ 2 + b + 3).factorization p = 0 := by
          exact Nat.factorization_eq_zero_of_non_prime (a ^ 2 + b + 3) H
        rw [this]
        apply Nat.zero_le

    -- Since this holds for every prime factor, we get $a^{2}+b+3 \leq (a+1)^{2}$.
    have h3 : a ^ 2 + b + 3 ≤ (a + 1) ^ 2 := by
      suffices a ^ 2 + b + 3 ∣ (a + 1 ) ^ 2 by
        apply Nat.le_of_dvd at this
        . exact this
        . exact Nat.zero_lt_succ ((((a + 1).pow 1).mul a).add (((a + 1).pow 0).mul a))
      rw [← Nat.factorization_le_iff_dvd, Nat.factorization_pow]
      . exact claim
      . omega
      . exact Ne.symm (Nat.zero_ne_add_one ((((a + 1).pow 1).mul a).add (((a + 1).pow 0).mul a)))

    -- There is no prime $p$ that occurs fewer times in $a^2 + b + 3$ than twice in $a + 1$.
    have h4 : ¬∃ p, Nat.Prime p ∧ (a ^  2 + b + 3).factorization p < 2 * (a + 1).factorization p := by
      by_contra G
      obtain ⟨ p, hpprime, hineq ⟩ := G
      have h1 : p * (a ^ 2 + b + 3) ≤ (a + 1) ^ 2 := by
        suffices (p * (a ^ 2 + b + 3)).factorization ≤ 2 • (a + 1).factorization by
          have h2 : 2 • (a + 1).factorization = ((a + 1) ^ 2).factorization := by symm; apply Nat.factorization_pow
          rw [h2] at this
          apply Nat.le_of_dvd
          . positivity
          . rw [← Nat.factorization_le_iff_dvd]
            . exact this
            . refine Nat.mul_ne_zero_iff.mpr ?_
              constructor
              . exact Nat.Prime.ne_zero hpprime
              . omega
            . omega

        intro q
        by_cases hpq : q = p
        . rw [Nat.factorization_mul]
          . calc
                (p.factorization + (a ^ 2 + b + 3).factorization) q
              = (p.factorization + (a ^ 2 + b + 3).factorization) p := by rw [hpq]
            _ = (p.factorization p) + (a ^ 2 + b + 3).factorization p := by exact rfl
            _ = 1 + (a ^ 2 + b + 3).factorization p := by congr; exact Nat.Prime.factorization_self hpprime
            _ ≤ 2 * (a + 1).factorization p := by exact Nat.one_add_le_iff.mpr hineq
            _ = _ := by simp; rw [← hpq]
          . exact Nat.Prime.ne_zero hpprime
          . omega
        . have : (p * (a ^ 2 + b + 3)).factorization q = (a ^ 2 + b + 3).factorization q := by
            rw [Nat.factorization_mul]
            . calc
                  (p.factorization + (a ^ 2 + b + 3).factorization) q
              _ = (p.factorization q) + (a ^ 2 + b + 3).factorization q := by exact rfl
              _ = 0 + (a ^ 2 + b + 3).factorization q := by
                  congr
                  by_cases hqprime : Nat.Prime q
                  . refine Nat.factorization_eq_zero_of_not_dvd ?_
                    by_contra G
                    apply hpq
                    exact (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp G
                  . exact Nat.factorization_eq_zero_of_non_prime p hqprime
              _ = _ := by rw [zero_add]
            . exact Nat.Prime.ne_zero hpprime
            . omega
          rw [this]
          apply claim

      have h2 : 2 * (a ^ 2 + b + 3) ≤ (a + 1) ^ 2 := by
        have : p ≥ 2 := by exact Nat.Prime.two_le hpprime
        exact mul_le_of_mul_le_right h1 this
      have h3 : (a + 1) ^ 2 < 2 * (a ^ 2 + b + 3):= by
        calc
          (a + 1) ^ 2 ≤ 2 * a ^ 2 + 2 := by nlinarith
          _ < 2 * a ^ 2 + 4 := by linarith
          _ ≤ 2 * (a ^ 2 + b + 3) := by omega
      linarith

    -- Hence, $a^2 + b + 3 = (a+1)^2$.
    have h5 : a ^ 2 + b + 3 = (a + 1) ^ 2 := by
      by_cases H : a ^ 2 + b + 3 < (a + 1) ^ 2
      . have : ∃ p, Nat.Prime p ∧ (a ^ 2 + b + 3).factorization p < ((a + 1)^2).factorization p := by
          by_contra G
          push_neg at G
          revert H
          simp
          apply Nat.le_of_dvd
          . omega
          . rw [← Nat.factorization_le_iff_dvd]
            . intro p
              by_cases hpprime : Nat.Prime p
              . exact G p hpprime
              . have : ((a + 1) ^ 2).factorization p = 0 := by exact Nat.factorization_eq_zero_of_non_prime _ hpprime
                rw [this]
                omega
            . omega
            . omega
        by_contra
        revert h4
        simp
        obtain ⟨ p , hpprime, hp ⟩ := this
        use p
        constructor
        . exact hpprime
        . rw [Nat.factorization_pow] at hp
          simp at hp
          exact hp
      . simp at H
        omega

    -- Consequently, $b = 2a - 2$.
    have h6 : (b : ℤ) = 2 * a - 2 := by zify at h5; linarith

    -- Thus, $ab+3b+8=a(2a-2)+3(2a-2)+9=2(a+1)^2$.
    have h7 : a * b + 3 * b + 8 = 2 * (a + 1) ^ 2 := by zify; rw [h6]; ring

    -- Thus, $n = 2$.
    qify at *
    rw [← hn, h5, h7]
    field_simp

  . intro hn
    use 2, 2
    simp
    constructor
    . intro p hp hp_dvd
      have : ¬p ^ 3 ∣ 3 ^ 2 := by
        intro h
        have h1 : p ∣ 3 ^ 2 := by
          have h2 : p ^ 3 ∣ 3 ^ 2 := h
          have h3 : p ∣ p ^ 3 := by
            exact dvd_pow (by rfl) (by norm_num)
          exact dvd_trans h3 h2
        have h2 : p ≤ 3 ^ 2 := by
          exact Nat.le_of_dvd (by norm_num) h1
        have h3 : p = 3 := by
          interval_cases p <;> norm_num at hp h1 ⊢
        rw [h3] at h
        norm_num at h
      norm_num at this
      contradiction
    . symm
      norm_num
      norm_cast