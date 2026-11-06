import Mathlib

/- 19.4.5 ** The sequence $a_{1}, a_{2}, \cdots$ is constructed as follows:
$a_{1}=2$; for each $n \geqslant 2, a_{n}$ is the largest prime factor of
$a_{1} \cdot a_{2} \cdots \cdots \cdot a_{n-1}+1$.
Prove: no term in this sequence equals 5. -/
theorem number_theory_143664 (a : ℕ → ℕ)
    (h₀ : a 1 = 2)
    (h₁ : ∀ n ≥ 2, IsGreatest {p | p.Prime ∧ p ∣ ∏ i in Finset.Icc 1 (n - 1), a i + 1} (a n)) :
    ∀ n, (n ≥ 1) → a n ≠ 5 := by

  -- Since $a_1 = 2$, $a_2$ is the largest prime factor of $a_1 + 1 = 3$,
  -- which is $3$.
  have h₂ : a 2 = 3 := by
    set ha2 := h₁ 2 (by rfl)
    simp at ha2
    simp [IsGreatest, upperBounds, h₀] at ha2
    obtain ⟨ ⟨ hlp, hldvd ⟩, hr ⟩ := ha2
    rw [← Nat.prime_dvd_prime_iff_eq hlp Nat.prime_three]
    exact hldvd

  -- We proceed by contradiction
  by_contra g
  push_neg at g
  -- Suppose that there exists $n$ with $a_n = 5$.
  obtain ⟨ n, ⟨ hn1 , hn ⟩  ⟩ := g
  have hngeq3 : n ≥ 3 := by
    by_contra g
    simp at g
    by_cases g' : n = 1
    . rw [g'] at hn
      simp [hn] at h₀
    . have : n = 2 := by omega
      rw [this] at hn
      simp [hn] at h₂

  have hngeq2 : n ≥ 2 := Nat.le_of_succ_le hngeq3

  -- Let $A = \prod_{i=1}^{n-1} a_i + 1$.
  set A := (∏ i in Finset.Icc 1 (n - 1), a i) + 1

  -- Note that $a_{k+2}$ is odd for all $k \geq 0$.
  have t1 (k : ℕ) : Odd (a (k + 2)) := by
    have hodd : Odd (∏ i ∈ Finset.Icc 1 (k + 1), a i + 1) := by
      rw [Finset.Icc_eq_cons_Ioc (by omega)]
      rw [Finset.prod_cons, h₀]
      apply odd_two_mul_add_one
    have : a (k + 2) ∣ ∏ i ∈ Finset.Icc 1 (k + 1), a i + 1 := by
      obtain hk2 := h₁ (k + 2) (by norm_num)
      simp [IsGreatest, upperBounds] at hk2
      obtain ⟨ ⟨ _, hdvd⟩ , _ ⟩ := hk2
      exact hdvd
    exact Odd.of_dvd_nat hodd this

  -- Since $a_1 = 2$ and $a_2 = 3$, the primes $2$ and $3$ do not divide $A$.
  -- As $5$ is the largest prime factor of $A$, we have $A = 5^m$ for some $m$.
  have claim1 : ∃ m : ℕ, m > 0 ∧ A = 5 ^ m := by
    have : ∀ d, d.Prime → d ∣ A → d = 5 := by
      intro d
      by_cases g : d < 5
      . intro dprime
        have h2or3 : d = 2 ∨ d = 3 := by revert d; decide
        obtain d2 | d3 := h2or3
        . rw [d2]
          intro ddvd
          have m1 : 1 ≡ A [MOD 2] := by
            unfold A
            rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.prod_cons, h₀]
            calc
              1 = 0 + 1 := by norm_num
              _ ≡ 2 * ∏ x ∈ Finset.Ioc 1 (n - 1), a x + 1 [MOD 2] := by
                    refine Nat.ModEq.add_right 1 ?_
                    apply Dvd.dvd.zero_modEq_nat
                    apply Nat.dvd_mul_right
          have m0 : 0 ≡ A [MOD 2] := by exact Dvd.dvd.zero_modEq_nat ddvd
          have : 0 ≡ 1 [MOD 2] := by exact Nat.ModEq.trans m0 (id (Nat.ModEq.symm m1))
          by_contra
          revert this
          decide
        . rw [d3]
          intro ddvd
          have m1 : 1 ≡ A [MOD 3] := by
            unfold A
            rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.prod_cons, h₀, mul_comm]
            have : Finset.Ioc 1 (n - 1) = Finset.Icc 2 (n - 1) := by exact rfl
            rw [this]
            rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.prod_cons, h₂, mul_assoc]
            calc
              1 = 0 + 1 := by norm_num
              _ ≡ _ [MOD 3]:= by refine Nat.ModEq.add_right 1 ?_
                                 apply Dvd.dvd.zero_modEq_nat
                                 apply Nat.dvd_mul_right
          have m0 : 0 ≡ A [MOD 3] := by exact Dvd.dvd.zero_modEq_nat ddvd
          have : 0 ≡ 1 [MOD 3] := by exact Nat.ModEq.trans m0 (id (Nat.ModEq.symm m1))
          by_contra
          revert this
          decide
      . by_cases g' : d = 5
        . exact fun _ _ ↦ g'
        . have d5 : d > 5 := by omega
          obtain h5 := h₁ n hngeq2
          simp [IsGreatest, hn, Nat.prime_five, upperBounds] at h5
          obtain ⟨ _, hmax ⟩ := h5
          unfold A
          intro dprime ddvd
          obtain hmaxd := @hmax d dprime ddvd
          omega
    use A.primeFactorsList.length
    constructor
    . have : ∃ d, d.Prime ∧ d ∣ A := by
        use A.minFac
        have : A ≠ 1 := by
          unfold A
          simp
          by_contra g
          have : ∃ i ∈ Finset.Icc 1 (n - 1), a i = 0 := by
            rw [Finset.prod_eq_zero_iff] at g
            exact g
          obtain ⟨ i, ⟨ hi, ai⟩ ⟩ := this
          by_cases gi : i = 1
          . rw [gi, h₀] at ai; simp at ai
          . have : i ≥ 2 := by
              revert hi
              simp
              omega
            have : ∃ k, i = k + 2 := by exact Nat.exists_eq_add_of_le' this
            obtain ⟨ k, hk ⟩ := this
            rw [hk] at ai
            obtain t1a1 := t1 k
            rw [ai] at t1a1
            revert t1a1
            decide

        constructor
        . refine Nat.minFac_prime this
        . exact Nat.minFac_dvd A
      obtain ⟨ d, hd ⟩ := this
      refine List.length_pos_iff_exists_mem.mpr ?_
      use d
      simp [hd]
    . apply Nat.eq_prime_pow_of_unique_prime_dvd
      . omega
      . apply this
  obtain ⟨ m, ⟨hmpos, hm⟩  ⟩ := claim1

  -- We can factor $A - 1$ as $(5 - 1)(1 + 5 + \cdots + 5^{m-1})$.
  have claim2 : A - 1 = (5 - 1) * (∑ i in Finset.range m, 5^i) := by
    rw [Nat.sub_mul, one_mul]
    have : 5 * ∑ i ∈ Finset.range m, 5 ^ i = ∑ i ∈ Finset.range m, 5 * 5 ^ i := by
      exact Finset.mul_sum (Finset.range m) (HPow.hPow 5) 5
    rw [this]
    symm
    calc
     _ = ∑ i ∈ Finset.range m, 5 * 5 ^ i - (5 ^ 0 + ∑ i ∈ Finset.Ico 1 m, 5 ^ i) := by
            rw [Finset.sum_range_eq_add_Ico (fun i ↦ 5 ^ i)]
            exact hmpos
     _ = _ :=  by rw [pow_zero, add_comm]
                  rw [Nat.sub_add_eq]
                  have :  ∑ i ∈ Finset.range m, 5 * 5 ^ i
                        = ∑ i ∈ Finset.range m, 5 ^ (i + 1) := by
                           refine Eq.symm (Finset.sum_congr rfl ?_)
                           intro x hx
                           ring
                  rw [this]
                  rw [Nat.range_eq_Icc_zero_sub_one]
                  have :  ∑ i ∈ Finset.Icc 0 (m - 1), 5 ^ (i + 1)
                        = ∑ i ∈ Finset.Icc 1 (m - 1 + 1), 5 ^ i := by
                    have :  ∑ i ∈ Finset.Ico 0 m , 5 ^ (i + 1)
                          = ∑ i ∈ Finset.Ico 1 (m + 1), 5 ^ i := by rw [Finset.sum_Ico_add']
                    calc
                      ∑ i ∈ Finset.Icc 0 (m - 1), 5 ^ (i + 1)
                      = ∑ i ∈ Finset.Ico 0 (m - 1 + 1) , 5 ^ (i + 1) := by exact rfl
                    _ = ∑ i ∈ Finset.Ico 0 m , 5 ^ (i + 1) := by rw [Nat.sub_add_cancel hmpos]
                    _ = ∑ i ∈ Finset.Ico 1 (m + 1), 5 ^ i := this
                    _ = ∑ i ∈ Finset.Ico 1 (m - 1 + 1 + 1), 5 ^ i := by rw [Nat.sub_add_cancel hmpos]
                    _ = _ := by exact rfl

                  . rw [this]
                    rw [Finset.sum_Icc_succ_top]
                    . have : Finset.Icc 1 (m - 1) = Finset.Ico 1 m := by apply Nat.Icc_pred_right 1 hmpos
                      rw [this, add_comm]
                      rw [Nat.add_sub_assoc, Nat.sub_add_cancel hmpos]
                      rw [hm]
                      simp
                      rfl
                    . simp
                  . exact Nat.not_eq_zero_of_lt hmpos

  -- But $5 - 1 = 4$. Hence, $4$ divides $A - 1 = \prod_{i = 1}^{n -1} a_i$.
  have claim3 : 4 ∣ (∏ i in Finset.Icc 1 (n - 1), a i) := by
    unfold A at claim2
    simp at claim2
    rw [claim2]
    apply Nat.dvd_mul_right

  -- But $a_1 = 2$$. Hence, $2$ divides $\prod_{i = 2}^{n -1} a_i$.
  have claim4 : 2 ∣ (∏ i in Finset.Icc 2 (n - 1), a i) := by
    rw [Finset.Icc_eq_cons_Ioc (by omega)] at claim3
    rw [Finset.prod_cons] at claim3
    rw [h₀] at claim3

    have : Finset.Ioc 1 (n - 1) = Finset.Icc 2 (n - 1) := by exact rfl
    rw [this] at claim3
    have : 4 = 2 * 2 := by rfl
    rw [this] at claim3
    apply Nat.dvd_of_mul_dvd_mul_left
    . have : 0 < 2 := by norm_num
      exact this
    . exact claim3

  have : ∃ s, n = s + 3 := by exact Nat.exists_eq_add_of_le' hngeq3
  obtain ⟨ s, hs ⟩ := this
  -- But $2$ does not divide $\prod_{i = 2}^{n-1} a_i$ since $a_i$ is odd for
  -- $i = 2,\ldots,n-1$.
  have claim5 : ¬2 ∣ (∏ i in Finset.Icc 2 (n - 1), a i) := by
    have t2 (r : ℕ) : Odd (∏ i in Finset.Icc 2 (r + 3 - 1), a i) := by
      induction r with
      | zero => simp [t1 0]
      | succ i ih =>
          have : Finset.Icc 2 (i + 1 + 2) = Finset.Icc 2 (i + 2 + 1) := by exact rfl
          simp
          rw [this]
          rw [← Nat.Icc_insert_succ_right]
          have :  ∏ i ∈ insert (i + 2 + 1) (Finset.Icc 2 (i + 2)), a i
                = (a (i + 2 + 1)) * (∏ i ∈ (Finset.Icc 2 (i + 2)), a i) := by
                  apply Finset.prod_insert
                  simp
          rw [this]
          exact Odd.mul (t1 (i + 1)) ih
          simp

    -- We therefore have a contradiction.
    obtain t := t2 (n - 3)
    rw [← even_iff_two_dvd]
    have : n - 3 + 3 - 1 = n - 1:= by omega
    rw [this] at t
    exact Nat.not_even_iff_odd.mpr t

  trivial