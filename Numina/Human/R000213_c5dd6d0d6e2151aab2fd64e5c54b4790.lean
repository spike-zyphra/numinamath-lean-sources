import Mathlib

/- Find the smallest positive integer  $m$  satisfying the following condition: for all  prime numbers  $p$  such that  $p>3$ ,have   $105|9^{ p^2}-29^p+m.$ -/
theorem number_theory_8586 (p : ℕ) (m : ℤ) (hp : p.Prime) (hp1 : 3 < p) :
  (m < 20 → 0 < m → ¬ 105 ∣ 9 ^ (p ^ 2) - 29 ^ p + m) ∧ (105 : ℤ)∣ 9 ^ (p ^ 2) - 29 ^ p + 20:= by
    -- $p$ is a odd number.
    have oddp : Odd p := Nat.Prime.odd_of_ne_two hp (by linarith)
    -- $p^2$ is a odd number.
    have oddp2 : Odd (p ^ 2) := Odd.pow oddp
    have h1 : (105 : ℤ) = 3 * 5 * 7 := by linarith
    --  \( 9 \equiv 0 \pmod{3} \) so \( 9^{p^2} \equiv 0 \pmod{3} \).
    have h31 : 9 ^ p ^ 2 ≡ 0 [ZMOD 3] := by
      refine Dvd.dvd.modEq_zero_int ?h
      refine Dvd.dvd.pow (by decide) (by positivity)
    -- \( 29 \equiv 2 \pmod{3} \). Since \( p \) is an odd prime, \( 2^p \equiv 2 \pmod{3} \)
    have h32 : 29 ^ p ≡ 2 [ZMOD 3] := by
      have : 29 ^ p ≡ 2 ^ p [ZMOD 3] := Int.ModEq.pow p rfl
      have h2 : 2 ^ p ≡ 2 [ZMOD 3] := by
        obtain ⟨t,ht⟩ := oddp
        simp [ht, pow_add, pow_mul]
        have : 4 ^ t ≡ 1 [ZMOD 3] := by rw [←one_pow t]; exact Int.ModEq.pow t rfl
        exact Int.ModEq.mul this (show 2 ≡ 2 [ZMOD 3] by rfl)
      exact this.trans h2
    -- So,
    -- \[
    -- 9^{p^2} - 29^p + m \equiv 0 - 2 + m \equiv m - 2 \equiv 0 \pmod{3} \implies m \equiv 2 \pmod{3}.
    -- \]
    have h3 : ∀ m, 9 ^ p ^ 2 - 29 ^ p + m ≡ m - 2 [ZMOD 3] := by
      intro n
      convert Int.ModEq.add (Int.ModEq.sub h31 h32 ) (show n ≡ n [ZMOD 3] by rfl) using 1
      abel
    -- - \( 9 \equiv 4 \pmod{5} \), so \( 9^{p^2} \equiv 4^{p^2} \).
    -- \( 29 \equiv 4 \pmod{5} \), so \( 29^p \equiv 4^p \).
    -- Since \( p \) is odd:
    -- \[
    -- 4^{p^2} \equiv 4 \pmod{5} \quad \text{and} \quad 4^p \equiv 4 \pmod{5}.
    -- \]
    have h51 : 9 ^ p ^ 2 ≡ 4 [ZMOD 5] := by
      have : 9 ^ p ^ 2 ≡ 4 ^ p ^ 2 [ZMOD 5] := Int.ModEq.pow (p ^ 2) rfl
      have h2 : 4 ^ p ^ 2 ≡ 4 [ZMOD 5] := by
        obtain ⟨t,ht⟩ := oddp2
        simp [ht, pow_add, pow_mul]
        have : 16 ^ t ≡ 1 [ZMOD 5] := by rw [←one_pow t]; exact Int.ModEq.pow t rfl
        exact Int.ModEq.mul this (show 4 ≡ 4 [ZMOD 5] by rfl)
      exact this.trans h2
    have h52 : 29 ^ p ≡ 4 [ZMOD 5] := by
      have : 29 ^ p ≡ 4 ^ p [ZMOD 5] := Int.ModEq.pow p rfl
      have h2 : 4 ^ p ≡ 4 [ZMOD 5] := by
        obtain ⟨t,ht⟩ := oddp
        simp [ht, pow_add, pow_mul]
        have : 16 ^ t ≡ 1 [ZMOD 5] := by rw [←one_pow t]; exact Int.ModEq.pow t rfl
        exact Int.ModEq.mul this (show 4 ≡ 4 [ZMOD 5] by rfl)
      exact this.trans h2
    --Thus,
    -- \[
    -- 9^{p^2} - 29^p + m \equiv 4 - 4 + m \equiv m \equiv 0 \pmod{5}.
    -- \]
    have h5 : ∀ m, 9 ^ p ^ 2 - 29 ^ p + m ≡ m [ZMOD 5] := by
      intro n
      convert Int.ModEq.add (Int.ModEq.sub h51 h52) (show n ≡ n [ZMOD 5] by rfl)
      simp
    -- - \( 9 \equiv 2 \pmod{7} \), so \( 9^{p^2} \equiv 2^{p^2} \).
    -- \( 29 \equiv 1 \pmod{7} \), so \( 29^p \equiv 1 \pmod{7} \).
    -- The order of 2 modulo 7 is 3. For any prime \( p > 3 \), \( p^2 \equiv 1 \pmod{3} \), hence:
    -- \[
    -- 2^{p^2} \equiv 2^{1} \equiv 2 \pmod{7}.
    -- \]
    have h71 : 9 ^ p ^ 2 ≡ 2 [ZMOD 7] := by
      have : 9 ^ p ^ 2 ≡ 2 ^ p ^ 2 [ZMOD 7] := Int.ModEq.pow (p ^ 2) rfl
      have h2 : 2 ^ p ^ 2 ≡ 2 [ZMOD 7] := by
        have : p ^ 2 = p ^ 2 - 1 + 1 :=
          Eq.symm (Nat.sub_add_cancel (Nat.one_le_pow 2 p (by linarith)))
        rw [this, pow_add]; simp
        have : 2 ^ (p ^ 2 - 1) ≡ 1 [ZMOD 7] := by
          have :  3 ∣ p ^ 2 - 1 := by
            -- 3 divides the product of three consecutive natural number.
            have h2 : ∀ n, 3 ∣ n * (n + 1) * (n + 2) := by
              intro n
              have h3 : n % 3 < 3 := Nat.mod_lt n (by linarith)
              set m := (n % 3) with hm
              interval_cases m
              · have := Nat.dvd_of_mod_eq_zero hm.symm
                rw [mul_assoc]; exact Dvd.dvd.mul_right this ((n + 1) * (n + 2))
              · have hm : (n + 2) % 3 = 0 := by rw [Nat.add_mod]; rw [←hm]
                have := Nat.dvd_of_mod_eq_zero hm
                exact Dvd.dvd.mul_left this (n * (n + 1))
              · have hm : (n + 1) % 3 = 0 := by rw [Nat.add_mod,←hm]
                have := Nat.dvd_of_mod_eq_zero hm
                nth_rw 2 [mul_comm]; rw [mul_assoc]
                exact Dvd.dvd.mul_right this (n * (n + 2))
            rw [←one_pow 2, Nat.sq_sub_sq]
            have h3 := h2 (p - 1)
            replace h3 : 3 ∣ p * (p - 1) * (p + 1) := by
              rw [show p - 1 + 1 = p by exact Nat.succ_pred_prime hp] at h3
              rw [show p - 1 + 2 = p + 1 by rw [←Nat.sub_add_comm (by linarith), Nat.add_sub_assoc (by linarith)]] at h3
              nth_rw 2 [mul_comm]; exact h3
            rw [mul_assoc] at h3
            have := Nat.dvd_gcd_mul_iff_dvd_mul.2 h3
            have h4 : (3).gcd p = 1 := by
              have : p.Coprime 3 := (Nat.Prime.coprime_iff_not_dvd hp).2
                (Nat.not_dvd_of_pos_of_lt (by positivity) hp1)
              exact Nat.coprime_comm.mp this
            simp [h4, mul_comm] at this
            exact this
          obtain ⟨k, hk⟩ := this
          simp [hk, pow_mul]
          rw [←one_pow k]
          exact Int.ModEq.pow k (by decide)
        exact Int.ModEq.mul this (show 2 ≡ 2 [ZMOD 7] by rfl)
      exact this.trans h2
    have h72 : 29 ^ p ≡ 1 [ZMOD 7] := by
      have : 29 ^ p ≡ 1 ^ p [ZMOD 7] := Int.ModEq.pow p rfl
      simp at this; exact this
    -- Thus,
    -- \[
    -- 9^{p^2} - 29^p + m \equiv 2 - 1 + m \equiv m + 1 \equiv 0 \pmod{7}
    -- \]
    have h7 : ∀ m, 9 ^ p ^ 2 - 29 ^ p + m ≡ m + 1 [ZMOD 7] := by
      intro m
      convert Int.ModEq.add (Int.ModEq.sub h71 h72) (show m ≡ m [ZMOD 7] by rfl) using 1
      abel
    -- $105 \mid 9 ^ (p ^ 2) - 29 ^ p + m$ if and only if `m ≡ 2 [ZMOD 3] ∧ m ≡ 0 [ZMOD 5] ∧ m ≡ 6 [ZMOD 7]`
    have aux : ∀ m, 105 ∣ 9 ^ (p ^ 2) - 29 ^ p + m ↔ m ≡ 2 [ZMOD 3] ∧ m ≡ 0 [ZMOD 5] ∧ m ≡ 6 [ZMOD 7] := by
      intro n
      constructor <;> intro h
      · have dvd3 : 3 ∣ (9 ^ (p ^ 2) - 29 ^ p + n : ℤ) := (show 3 ∣ (105 : ℤ) by decide).trans h
        have dvd5 : 5 ∣ (9 ^ (p ^ 2) - 29 ^ p + n : ℤ) := (show 5 ∣ (105 : ℤ) by decide).trans h
        have dvd7 : 7 ∣ (9 ^ (p ^ 2) - 29 ^ p + n : ℤ) := (show 7 ∣ (105 : ℤ) by decide).trans h
        have dvd3' : 0 ≡ 9 ^ (p ^ 2) - 29 ^ p + n [ZMOD 3] := Int.modEq_of_dvd (by simpa)
        have dvd5' : 0 ≡ 9 ^ (p ^ 2) - 29 ^ p + n [ZMOD 5] := Int.modEq_of_dvd (by simpa)
        have dvd7' : 0 ≡ 9 ^ (p ^ 2) - 29 ^ p + n [ZMOD 7] := Int.modEq_of_dvd (by simpa)
        have zmod3 : n ≡ 2 [ZMOD 3] := by
          have := Int.ModEq.add_right 2 (dvd3'.trans (h3 n))
          simp at this
          exact this.symm
        have zmod5 : n ≡ 0 [ZMOD 5] := by
          have := Int.ModEq.add_right 0 (dvd5'.trans (h5 n))
          simp at this; exact this.symm
        have zmod7 : n ≡ 6 [ZMOD 7] := by
          have := Int.ModEq.add_right 6 (dvd7'.trans (h7 n))
          simp [add_assoc] at this
          exact (this.trans (by simp)).symm
        exact ⟨zmod3, zmod5, zmod7⟩
      · have dvd3 : 3 ∣ (9 ^ p ^ 2 - 29 ^ p + n ) := by
          have : 9 ^ p ^ 2 - 29 ^ p + n ≡ 0 [ZMOD 3] :=
          (h3 n).trans (Int.ModEq.sub h.1 (show 2 ≡ 2 [ZMOD3] by rfl))
          convert Int.modEq_iff_dvd.1 this.symm using 1; simp
        have dvd5 : 5 ∣ (9 ^ p ^ 2 - 29 ^ p + n ) := by
          have : 9 ^ p ^ 2 - 29 ^ p + n ≡ 0 [ZMOD 5] :=
          (h5 n).trans h.2.1
          convert Int.modEq_iff_dvd.1 this.symm using 1; simp
        have dvd7 : 7 ∣ (9 ^ p ^ 2 - 29 ^ p + n ) := by
          have : 9 ^ p ^ 2 - 29 ^ p + n ≡ 0 [ZMOD 7] :=
          (h7 n).trans (Int.ModEq.add h.2.2 (show 1 ≡ 1 [ZMOD 7] by rfl))
          convert Int.modEq_iff_dvd.1 this.symm using 1; simp
        have : 5 * 7 ∣ 9 ^ p ^ 2 - 29 ^ p + n := by
          exact IsCoprime.mul_dvd (show IsCoprime 5 7 by exact Int.isCoprime_iff_gcd_eq_one.mpr rfl) dvd5 dvd7
        rw [h1, mul_assoc]
        exact IsCoprime.mul_dvd (show IsCoprime 3 (5 * 7) by exact Int.isCoprime_iff_gcd_eq_one.mpr rfl) dvd3 this
    constructor
    · intro hm1 hm2 h2
      rw [aux m] at h2
      -- for $m < 20$, using `interval_cases` and `tauto` to check that $m$ not satisfy the condition.
      interval_cases m <;> tauto
    · -- check that when $m = 20$, the condition is satisfied.
      have : 20 ≡ 2 [ZMOD 3] ∧ 20 ≡ 0 [ZMOD 5] ∧ 20 ≡ 6 [ZMOD 7] := by decide
      exact (aux 20).2 this