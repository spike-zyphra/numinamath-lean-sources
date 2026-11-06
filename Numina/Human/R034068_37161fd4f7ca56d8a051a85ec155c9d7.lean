import Mathlib

/- Soit $\left(a_{n}\right)_{n \in \mathbb{N}}$ une suite croissante et non constante d'entiers strictement positifs tels que $a_{n}$ divise $n^{2}$ pour tout $n \geqslant 1$. Prouver que l'une des affirmations suivantes est vraie:
a) Il existe un entier $n_{1}>0$ tel que $a_{n}=n$ pour tout $n \geqslant n_{1}$.
b) Il existe un entier $n_{2}>0$ tel que $a_{n}=n^{2}$ pour tout $n \geqslant n_{2}$. -/
theorem number_theory_604407 (a : ℕ → ℕ) (ham : Monotone a)
    (hav : ¬ (∃ (c : ℕ), ∀ (n : ℕ), a n =c))
    (hpos : ∀ n, 0 < a n) (hdiv : ∀ n, a n ∣ n ^ 2) :
    (∃ n1, 0 < n1 ∧ ∀ n ≥ n1, a n = n) ∨
    (∃ n2, 0 < n2 ∧ ∀ n ≥ n2, a n = n ^ 2) := by 
    unfold Monotone at ham
    --First, since for all integers $n$, we have $a_{n} \in \mathbb{N}^{\*}$, and the sequence $(a_{n})$ is increasing and not constant, there exists an integer $n_{0}$ such that $a_{n} \geqslant 2$ for all $n \geqslant n_{0}$.
    have ha1 : ∃ (n₀ : ℕ), ∀ (n : ℕ), (n ≥ n₀) → a n ≥ 2 := by
      by_contra! hc
      absurd hav
      use 1
      intro n
      obtain ⟨n₁, ⟨hn₁, han₁⟩⟩ := hc n
      have han₁1 : a n₁ = 1 := by 
        exact Nat.eq_of_le_of_lt_succ (hpos n₁) han₁
      have hanleq1 : a n ≤ 1 := by
        rw [← han₁1]
        exact ham hn₁
      exact Eq.symm (Nat.le_antisymm (hpos n) hanleq1)
    obtain ⟨n₀, han₀⟩ := ha1
    --Consequently, for any prime number $p &gt; n_{0}$, we have $a_{p}=p$ or $a_{p}=p^{2}$.
    have hp : ∀ (p : ℕ), p.Prime ∧ p ≥ n₀ → a p = p ∨ a p = p ^ 2 := by
      intro p ⟨hp, hpg⟩
      have hp1 : a p ≥ 2 := by 
        exact han₀ p hpg
      have hp2 : a p ∣ p ^ 2 := by
        exact hdiv p
      have hap : (p ^ 2).divisors = {p ^ 2, p, 1} := by
        exact Nat.Prime.divisors_sq hp
      have hap1 : a p ∈ (p ^ 2).divisors := by
        apply Nat.mem_divisors.mpr
        constructor
        · exact hp2
        · apply pow_ne_zero 2
          exact Nat.Prime.ne_zero hp
      rw [hap] at hap1
      simp at hap1
      cases' hap1 with hap2 hap3
      · right; exact hap2
      · cases' hap3 with hap4 hap5
        · left; exact hap4
        · absurd hap5
          push_neg
          linarith [hp1]
    by_cases hann : ∀ (n : ℕ), n ≥ 1 → a n ≤ n
    · --- Suppose that for all integers $n \geqslant 1$, we have $a_{n} \leqslant n$. 
      left
      --Let $p &gt; n_{0}$ be a prime number.
      have h1p : ∃ (p : ℕ), n₀ ≤ p ∧ Nat.Prime p := by
        exact Nat.exists_infinite_primes n₀
      obtain ⟨p, ⟨hp11, hp12⟩⟩ := h1p
      --We will prove by induction that $a_{n}=n$ for all $n \geqslant p$.
      use p
      constructor
      · exact Nat.Prime.pos hp12
      · have hk : ∀ (k : ℕ), a (p + k) = p + k := by
          intro k
          induction' k with k hk
          · --Indeed, from the above, we have $a_{p}=p$.
            simp only [add_zero]
            have : a p = p ∨ a p = p ^ 2 := by
              apply hp
              constructor
              · exact hp12
              · exact hp11
            cases' this with hap1 hap2
            · exact hap1
            · absurd hann
              push_neg
              use p
              rw [hap2]
              have : p ≥ 2 := by exact Nat.Prime.two_le hp12
              constructor
              · exact Nat.one_le_of_lt this
              · apply lt_self_pow₀ this
                norm_num
          · --Furthermore, if $a_{n}=n$ for some $n \geqslant p \geqslant 2$,
            --then $n=a_{n} \leqslant a_{n+1} \leqslant n+1$,
            have hpk1 : p + k ≤ a (p + (k + 1)) := by
              rw [← hk]
              apply ham
              simp only [add_le_add_iff_left, le_add_iff_nonneg_right, zero_le]
            have hpk2 : a (p + (k + 1)) ≤ p + k + 1 := by
              apply hann
              linarith
            --hence $a_{n+1}=n$ or $a_{n+1}=n+1$.
            have hpk3 : a (p + (k + 1)) = p + k ∨ a (p + (k + 1)) = p + k + 1 := by
              apply Nat.le_and_le_add_one_iff.mp
              exact ⟨hpk1, hpk2⟩
            cases' hpk3 with h1 h2
            · --However, $a_{n+1}$ divides $(n+1)^{2}$, while $n$ does not divide $(n+1)^{2}$.
              absurd hdiv
              push_neg
              use (p + (k + 1))
              rw [h1]
              let t := p + k
              show ¬ t ∣ (t + 1) ^ 2
              have hleft : (t + 1) ^ 2 > t * (t + 2) := by  
                linarith
              have hright : (t + 1) ^ 2 < t * (t + 2 + 1) := by
                have : t > 1 := by 
                  apply Nat.lt_add_right k
                  exact Nat.Prime.one_lt hp12
                calc
                _ = t ^ 2 + 2 * t + 1 := by ring
                _ < t ^ 2 + 2 * t + t := by 
                  exact Nat.add_lt_add_left this (t ^ 2 + 2 * t)
                _ = _ := by ring
              exact Nat.not_dvd_of_between_consec_multiples hleft hright
            · --Thus, we have $a_{n+1}=n+1$, which completes the induction.
              exact h2
        --It is then sufficient to choose $n_{1}=p$ to conclude in this case.
        intro n hn
        have : n = p + (n - p) := by omega
        rw [this, hk]
    · --- Suppose there exists an integer $m \geqslant 1$ such that $a_{m}&gt;m$.
      right
      push_neg at hann
      obtain ⟨m, ⟨hm1, hm2⟩⟩ := hann
      --Since these are integers, it follows that $a_{m} \geqslant m+1$.
      have h2p : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ p > n := by
        intro n
        obtain ⟨p, hp_prime, hp_gt⟩ := Nat.exists_infinite_primes (n + 1)
        have : ∃ q, Nat.Prime q ∧ Odd q ∧ q > n := by
          by_cases h : p = 2
          · use 3
            norm_num
            constructor
            · exact Nat.odd_iff.mpr rfl
            · rw [h] at hp_prime
              linarith [hp_prime]
          · use p
            constructor
            · exact hp_gt
            · constructor
              · exact Nat.Prime.odd_of_ne_two hp_gt h
              · exact hp_prime
        exact this
      obtain ⟨p, hpn2, ⟨hpn3, hpn1⟩⟩ := h2p m
      --Let $p &gt; m$ be an odd prime number.
      use p
      constructor
      · exact Nat.Prime.pos hpn2
      · have hm3 : a m ≥ m + 1 := by
          exact hm2
        have hm4 : m + 1 ≥ 2 := by
          exact Nat.le_add_of_sub_le hm1
        have hm5 : ∀ (k : ℕ), a (m + k) ≥  m + k + 2 := by
          intro k
          induction' k with k hk
          · --But, $m+1 \geqslant 2$ and $m+1$ is coprime with $m^{2}$, so $m+1$ cannot divide $m^{2}$, and we have $a_{m} \geqslant m+2$.
            rw [add_zero]
            have hm6 : a m ≠ m + 1 := by
              by_contra hm7
              absurd hdiv
              push_neg
              use m
              rw [hm7]
              have hleft : m ^ 2 > (m + 1) * (m - 1) := by
                have : (m + 1) * (m - 1) = m * m - 1 := by
                  exact Eq.symm (mul_self_tsub_one m)
                rw [this]
                have hm8 : m * m = m ^ 2 := by
                  exact Eq.symm (Nat.pow_two m)
                rw [hm8]
                simp only [gt_iff_lt, tsub_lt_self_iff, zero_lt_one, and_true]
                exact Nat.pos_pow_of_pos 2 hm1
              have hright : m ^ 2 < (m + 1) * (m - 1 + 1) := by
                have hm9 : m - 1 + 1 = m := by
                  exact Nat.sub_add_cancel hm1
                rw [hm9]
                rw [add_mul, Nat.pow_two, one_mul]
                simp only [lt_add_iff_pos_right, gt_iff_lt]
                exact hm1
              exact Nat.not_dvd_of_between_consec_multiples hleft hright
            by_contra hm10
            push_neg at hm10
            absurd hm6
            exact Nat.eq_of_le_of_lt_succ hm2 hm10
          · --We deduce that $a_{m+1} \geqslant a_{m}&gt;m+1$. An immediate induction ensures that $a_{n}&gt;n$ for all $n \geqslant m$.
            have : a (m + k + 1) ≥ a (m + k) := by
              apply ham
              norm_num
            have hk1 : a (m + k + 1) ≥ m + k + 2 :=
              calc
              _ ≥ a (m + k) := by exact this
              _ ≥ _ := by exact hk
            have hk2 : a (m + k + 1) ≠ m + k + 2 := by
              by_contra hk3
              absurd hdiv
              push_neg
              use m + k + 1
              rw [hk3]
              let l := m + k + 1
              show ¬ l + 1 ∣ l ^ 2
              have hleft : l ^ 2 > (l + 1) * (l - 1) := by
                have hl1 : (l + 1) * (l - 1) = l * l - 1 := by
                  exact Eq.symm (mul_self_tsub_one l)
                rw [hl1]
                rw [Nat.pow_two]
                simp only [gt_iff_lt, tsub_lt_self_iff, Nat.zero_lt_succ, mul_pos_iff_of_pos_left,
                  zero_lt_one, and_self]
              have hright : l ^ 2 < (l + 1) * l := by
                rw [add_mul, one_mul, Nat.pow_two]
                simp only [lt_add_iff_pos_right, Nat.zero_lt_succ]
              exact Nat.not_dvd_of_between_consec_multiples hleft hright
            have : a (m + k + 1) > m + k + 2 := by
              exact Nat.lt_of_le_of_ne hk1 (id (Ne.symm hk2))
            exact this
        --In particular, given our initial remark, if $p \geqslant m$ is a prime number, we have $a_{p}=p^{2}$.
        have hp1 : a p = p ^ 2 := by
          have hp2 : a p ≥ p + 2 := by
            have : p = m + (p - m) := by omega
            rw [this]
            exact hm5 (p - m)
          have hp3 : (p ^ 2).divisors = {p ^ 2, p, 1}:= by
            exact Nat.Prime.divisors_sq hpn2
          have hp4 : a p ∈ (p ^ 2).divisors := by
            apply Nat.mem_divisors.mpr
            constructor
            · exact hdiv p
            · apply pow_ne_zero 2
              exact Nat.Prime.ne_zero hpn2
          rw [hp3] at hp4
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp4
          cases' hp4 with hp41 hp42
          · exact hp41
          · cases' hp42 with hp42 hp43 
            · absurd hp2
              push_neg
              rw [hp42]
              omega
            · absurd hp2
              push_neg
              rw [hp43]
              omega
        intro n hn
        have hsub : n = p + (n - p) := by omega
        rw [hsub]
        --We will prove by induction that $a_{n}=n^{2}$ for all $n \geqslant p$.
        induction' (n - p) with k hk
        · --We have just seen that this is true for $n=p$.
          simp only [add_zero, hp1]
        · --Suppose that $a_{n}=n^{2}$ for some integer $n \geqslant p$.
          let q := p + k
          show a (q + 1) = (q + 1) ^ 2
          have hq1 : a (q + 1) ≥ q ^ 2 := by
            rw [← hk]
            apply ham
            simp only [le_add_iff_nonneg_right, zero_le]  
          have hq2 : q ^ 2 > (q + 1) ^ 2 / 2 := by
            have hq3 : 2 * q ^ 2 > (q + 1) ^ 2 := by
              have hq4 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by
                ring
              rw [hq4]
              have hq5 : q ^ 2 > 2 * q + 1 := by
                show q ^ 2 ≥ 2 * q + 2
                rw [Nat.pow_two]
                have : q * q ≥ 3 * q := by
                  apply Nat.mul_le_mul_right q
                  have hpgeq3 : 3 ≤ p := by
                    by_contra! hpeq2
                    have : p ≥ 2 := by
                      exact Nat.Prime.two_le hpn2
                    have : p = 2 := by
                      linarith [this, hpeq2]
                    absurd hpn3
                    rw [this]
                    norm_num
                  exact Nat.le_add_right_of_le hpgeq3
                calc
                  _ ≥ 3 * q := by apply this
                  _ > 2 * q + 1 := by 
                    omega
              rw [two_mul, add_assoc]
              exact Nat.add_lt_add_left hq5 (q ^ 2)
            exact Nat.div_lt_of_lt_mul hq3
          --Then $n \geqslant 3$, hence $a_{n+1} \geqslant a_{n}=n^{2}&gt;\frac{1}{2}(n+1)^{2}$.
          have hq6 : a (q + 1) > (q + 1) ^ 2 / 2 :=
            calc
            _ ≥ q ^ 2 := by apply hq1
            _ > _ := by apply hq2
          --Since $a_{n+1}$ divides $(n+1)^{2}$, we have $a_{n+1}=(n+1)^{2}$. This completes the induction.
          have hq7 : a (q + 1) ∣ (q + 1) ^ 2 := by
            exact hdiv (q + 1)
          unfold Dvd.dvd at hq7
          unfold Nat.instDvd at hq7
          rcases hq7 with ⟨u, hu⟩
          have hu1 : u < 2 := by
            by_contra! hu2
            have hu3 : a (q + 1) * 2 ≤ a (q + 1) * u := by
              apply Nat.mul_le_mul_left
              exact Nat.succ_le_of_lt hu2
            rw [← hu] at hu3
            absurd hu3
            push_neg
            calc
            _ = ((q + 1) ^ 2 / 2) * 2 := by omega
            _ < _ := by 
              apply Nat.mul_lt_mul_of_pos_right hq6
              exact two_pos
          have hu4 : u = 1 := by
            by_contra! hu5
            have hu6 : u = 0 := by
              apply Nat.lt_one_iff.mp 
              apply Nat.lt_of_le_of_ne _ hu5
              exact Nat.le_of_lt_succ hu1
            rw [hu6] at hu
            simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false] at hu
          --It is therefore sufficient to choose $n_{2}=p$ to conclude in this case.
          rw [hu4] at hu
          rw [hu, mul_one]
