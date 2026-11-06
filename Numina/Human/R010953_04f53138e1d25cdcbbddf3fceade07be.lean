import Mathlib

/- Let $m, n \geq 2$ be integers such that $\gcd(m, n-1) = \gcd(m, n) = 1$. Prove that among the sequence $a_1, a_2, \ldots, a_{m-1}$, where $a_1 = mn + 1$ and $a_{k+1} = na_k + 1$ for $1 \leq k \leq m-2$, there is at least one composite number. -/
theorem number_theory_8957 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hmgcd : Nat.gcd m (n - 1) = 1) (hmgcd' : Nat.gcd m n = 1)
    (a : ℕ → ℕ) (ha : a 1 = m * n + 1)
    (hak : ∀ k ≥ 1, a (k + 1) = n * a k + 1) :
    ∃ i ∈ Finset.Icc 1 (m - 1), ¬Nat.Prime (a i) := by

  -- We first show that if $k$ is a positive integer, then
  -- $n^k - 1 = (n-1)\sum_{i=0}^{k-1} n^i$.
  have claim1 (k : ℕ) (hk : k > 0) : n ^ k - 1 = (n - 1) * (∑ i in Finset.range k, n^i) := by
    rw [Nat.sub_mul, one_mul]
    have : n * ∑ i ∈ Finset.range k, n ^ i = ∑ i ∈ Finset.range k, n * n ^ i := by
      exact Finset.mul_sum (Finset.range k) (HPow.hPow n) n
    rw [this]
    symm
    calc
     _ = ∑ i ∈ Finset.range k, n * n ^ i - (n ^ 0 + ∑ i ∈ Finset.Ico 1 k, n ^ i) := by
            rw [Finset.sum_range_eq_add_Ico (fun i ↦ n ^ i)]
            exact hk
     _ = _ :=  by rw [pow_zero, add_comm]
                  rw [Nat.sub_add_eq]
                  have :  ∑ i ∈ Finset.range k, n * n ^ i
                        = ∑ i ∈ Finset.range k, n ^ (i + 1) := by
                           refine Eq.symm (Finset.sum_congr rfl ?_)
                           intro x hx
                           ring
                  rw [this]
                  rw [Nat.range_eq_Icc_zero_sub_one]
                  have :  ∑ i ∈ Finset.Icc 0 (k - 1), n ^ (i + 1)
                        = ∑ i ∈ Finset.Icc 1 (k - 1 + 1), n ^ i := by
                    have :  ∑ i ∈ Finset.Ico 0 k , n ^ (i + 1)
                          = ∑ i ∈ Finset.Ico 1 (k + 1), n ^ i := by rw [Finset.sum_Ico_add']
                    calc
                      ∑ i ∈ Finset.Icc 0 (k - 1), n ^ (i + 1)
                      = ∑ i ∈ Finset.Ico 0 (k - 1 + 1) , n ^ (i + 1) := by exact rfl
                    _ = ∑ i ∈ Finset.Ico 0 k , n ^ (i + 1) := by rw [Nat.sub_add_cancel hk]
                    _ = ∑ i ∈ Finset.Ico 1 (k + 1), n ^ i := this
                    _ = ∑ i ∈ Finset.Ico 1 (k - 1 + 1 + 1), n ^ i := by rw [Nat.sub_add_cancel hk]
                    _ = _ := by exact rfl

                  . rw [this]
                    rw [Finset.sum_Icc_succ_top]
                    . have : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by apply Nat.Icc_pred_right 1 hk
                      rw [this, add_comm]
                      rw [Nat.add_sub_assoc, Nat.sub_add_cancel hk]
                      simp
                      rfl
                    . simp
                  . exact Nat.not_eq_zero_of_lt hk

  -- It then follows that if $k$ is a positive integer, then $((n^k - 1)/(n-1))(n-1)=n^k-1$.
  have claim1' (k : ℕ) (hk : k > 0) : (n ^ k - 1) / (n - 1) * (n - 1) = n ^ k - 1 := by
    rw [claim1 k]
    rw [mul_comm (n - 1)]
    have : (∑ i ∈ Finset.range k, n ^ i) * (n - 1) / (n - 1) = (∑ i ∈ Finset.range k, n ^ i) := by
      apply Nat.mul_div_left
      omega
    rw [this]
    exact hk

  -- It is an easy induction to show that for all $i=1,\ldots,m-1, a_i = mn^i + (n^i-1)/(n-1)$.
  have claim2 : ∀ i ∈ Finset.Icc 1 (m - 1), a i = m * n ^ i + (n ^ i - 1) / (n - 1) := by
    intro i
    induction i with
    | zero => simp
    | succ k ih =>
      by_cases hk : k = 0
      . simp [hk]
        intro g
        simp [ha]
        refine Eq.symm (Nat.div_self ?_)
        exact Nat.zero_lt_sub_of_lt hn
      . by_cases h : k ≥ m - 1
        . intro g
          simp at g
          omega
        . replace hk : 1 ≤ k := by exact Nat.one_le_iff_ne_zero.mpr hk
          simp at ih h
          intro g
          have : k ≤ m - 1 := by omega
          replace ih := ih hk this
          rw [hak k hk, ih]
          calc
                n * (m * n ^ k + (n ^ k - 1) / (n - 1)) + 1
            _ = m * n ^ (k + 1) + (n * ((n ^ k - 1) / (n - 1)) + 1) := by ring
            _ = _ := by rw [Nat.add_left_cancel_iff]
                        suffices  (n * ((n ^ k - 1) / (n - 1)) + 1) * (n - 1)
                                = (n ^ (k + 1) - 1) / (n - 1) * (n - 1) by
                            refine Eq.symm (Nat.div_eq_of_eq_mul_left ?_ ?_)
                            . omega
                            . rw [add_mul, one_mul, mul_assoc]
                              rw [claim1' k (by omega)]
                              rw [Nat.mul_sub, mul_one]
                              symm
                              calc
                                _ = n ^ (k + 1) - n + (n - 1) := by ring_nf
                                _ = (n ^ (k + 1) - n + n) - 1 := by
                                      refine Eq.symm (Nat.add_sub_assoc ?_ (n ^ (k + 1) - n))
                                      omega
                                _ = n ^ (k + 1) - 1 := by
                                      rw [Nat.sub_add_cancel]
                                      rw [pow_add, pow_one]
                                      refine Nat.le_mul_of_pos_left n ?_
                                      refine Nat.pow_pos ?_
                                      omega
                        rw [claim1' (k + 1) (by omega)]
                        rw [add_mul, mul_assoc, claim1' k (by omega), one_mul]
                        rw [Nat.mul_sub, mul_one]
                        calc
                          _ = n ^ (k + 1) - n + (n - 1) := by ring_nf
                          _ = (n ^ (k + 1) - n + n) - 1 := by
                                refine Eq.symm (Nat.add_sub_assoc ?_ (n ^ (k + 1) - n))
                                omega
                          _ = n ^ (k + 1) - 1 := by
                                rw [Nat.sub_add_cancel]
                                rw [pow_add, pow_one]
                                refine Nat.le_mul_of_pos_left n ?_
                                refine Nat.pow_pos ?_
                                omega

  -- We will need Fermat's Little Theorem, which states that if $p$ is a prime
  -- $a$ and $p$ are coprime, then $a^{p-1}$ is congruent to 1 modulo $p$.
  have fermatLittle {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) : a^(p-1) ≡ 1 [MOD p] := by
    have : IsCoprime (a : ℤ) (p : ℤ) := by simp [Int.coprime_iff_nat_coprime]
                                           exact ha

    let fermat := @Int.ModEq.pow_card_sub_one_eq_one p hp a this
    rw [← Int.natCast_modEq_iff]
    ring_nf
    have : ∃ m : ℕ, p = m + 1 := by refine Nat.exists_eq_add_of_le' ?_; exact Nat.Prime.one_le hp
    obtain ⟨ m, hm ⟩ := this
    rw [hm]
    rw [hm] at fermat
    simp at *
    exact fermat

  -- Let $p$ be the minimum prime factor of $m$.
  set p := m.minFac

  -- Clearly, $p$ is prime.
  have hp : Nat.Prime p := by refine Nat.minFac_prime ?_; omega

  -- Also, $1 \leq p - 1$ since $p$, being a prime, is at least 2.
  have pbd : 1 ≤ p - 1 := by
    have : 2 ≤ p := by exact Nat.Prime.two_le hp
    omega

  -- We also have $p \leq m$ since $p$ is a prime factor
  -- of $m$ and $m$ is positive.
  have g₁ : p ≤ m := by simp [p]; refine Nat.minFac_le ?_; omega

  -- If $r$ is a positive integer such that $gcd(m, r) = 1$,
  -- then $gcd(p, r) = 1$.
  have hgcd (r : ℕ) (hr : 0 < r)
    (hcoprime : Nat.gcd m r = 1) : Nat.gcd p r = 1 := by
    have dvd_p : p ∣ m := by exact Nat.minFac_dvd m
    have h1 : p.Coprime r := by
      apply Nat.Coprime.of_dvd_left (show p ∣ m by exact dvd_p)
      exact hcoprime
    exact h1

  -- We show that $a_{p-1}$ is composite.
  use (p - 1)

  constructor
  . -- Clearly, we have $1 \leq p - 1 \leq m - 1$ since $p \leq m$.
    simp
    constructor
    . exact pbd
    . rw [Nat.sub_add_cancel]
      . simp [p]; refine Nat.minFac_le ?_; omega
      . omega

  . -- Note that $p$ divides $n^{p-1}-1$ by Fermat's Little Theorem
    have h₀ : p ∣ n ^ (p - 1) - 1 := by
      have : 1 ≡ n ^ (p - 1) [MOD p]:= by
        symm
        apply fermatLittle
        . exact hp
        . have : p.gcd n = 1 := by
            apply hgcd n
            . omega
            . exact hmgcd'
          exact Nat.coprime_comm.mp this
      refine (Nat.modEq_iff_dvd' ?_).mp this
      refine Nat.one_le_pow (p - 1) n ?_
      omega

    -- Since $a_{p-1} = m * n^{p-1} + (n^{p-1}-1) / (n - 1)$
    -- and $p$ divides $mn^{p-1}$ because $p$ divides $m$
    -- and $p$ divides $n^{p-1}=(n-1)\sum_{i=0}{p-2} n^i)$
    -- but does not divide $n-1$, we have that $p$ divides $a_{p-1}$.
    have h₁ : p ∣ a (p - 1) := by
      rw [claim2 (p - 1)]
      . refine Nat.dvd_add ?_ ?_
        . have : ∃ r, m = p * r := by refine exists_eq_mul_right_of_dvd ?_; exact Nat.minFac_dvd m
          obtain ⟨ r, hr ⟩ := this
          rw [hr, mul_assoc]
          apply Nat.dvd_mul_right
        . rw [claim1 (p - 1) (by omega)] at h₀ ⊢
          rw [mul_comm]
          rw [Nat.mul_div_left]
          . have : p.gcd (n - 1) = 1 := by
              apply hgcd (n - 1)
              . omega
              . exact hmgcd
            exact Nat.Coprime.dvd_of_dvd_mul_left this h₀
          . omega
      . simp
        constructor
        . exact pbd
        . rw [Nat.sub_add_cancel]
          . simp [p]; refine Nat.minFac_le ?_; omega
          . omega

    -- Note that $p < a_{p-1}$.
    have g₂ : p < a (p - 1) := by
        obtain h₃ := claim2 (p - 1)
        simp at h₃
        replace h₃ := h₃ pbd
        rw [h₃]
        . suffices p < m * n ^ (p - 1) by exact Nat.lt_add_right ((n ^ (p - 1) - 1) / (n - 1)) this
          suffices 1 < n ^ (p - 1) by
            calc
              _ = p * 1 := by rw [mul_one]
              _ ≤ m * 1 := by exact Nat.mul_le_mul_right 1 g₁
              _ < m * n ^ (p - 1) := by apply Nat.mul_lt_mul_of_pos_left
                                        . exact this
                                        . omega
          refine Nat.one_lt_pow ?_ hn
          omega
        . rw [Nat.sub_add_cancel]
          . exact g₁
          . omega

    -- $a_{p-1}$ is not a prime because $p$ is a prime that divides it
    -- and $p < a_{p-1}$.
    rw [Nat.not_prime_iff_exists_dvd_ne]
    . use p
      simp [h₁]
      constructor
      . omega
      . exact Nat.ne_of_lt g₂
    . apply Nat.le_trans (Nat.Prime.two_le hp) (Nat.le_of_succ_le g₂)