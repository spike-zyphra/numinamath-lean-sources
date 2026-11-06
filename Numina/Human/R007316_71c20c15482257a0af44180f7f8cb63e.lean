import Mathlib

/- Déterminer tous les entiers strictement positifs a et $b$ tels que $4 \boldsymbol{a}+1$ et $4 \boldsymbol{b}-1$ soient premiers entre eux, et tels que $a+b$ divise $16 a b+1$. -/
theorem number_theory_607599 :
    {(a, b) : ℕ × ℕ | 0 < a ∧ 0 < b ∧ Nat.Coprime (4 * a + 1) (4 * b - 1) ∧ a + b ∣ 16 * a * b + 1} = {(a, 3 * a - 1) | (a : ℕ) (ha : a > 0)} ∪ {(3 * b + 1, b) | (b : ℕ) (hb : b > 0)} := by
  -- Simplify the goal into two parts.
  ext ⟨a, b⟩
  -- First, prove a lemma that Nat.gcd (a + b) (4 * a + 1) = 1 if and only if 4a + 1 and 4b - 1 are coprime.
  have lm (ha : 0 < a) (hb : 0 < b) : Nat.gcd (a + b) (4 * a + 1) = 1 ↔ Nat.Coprime (4 * a + 1) (4 * b - 1) := by
    -- Note that 4 and 4a + 1 are coprime.
    have : Nat.Coprime 4 (4 * a + 1) := by
      -- Use Euclidean algorithm.
      apply Nat.gcd_mul_left_add_right
    rw [Nat.coprime_iff_gcd_eq_one]
    calc
      _ ↔ (4 * (a + b)).gcd (4 * a + 1) = 1 := by
        rw [<-Nat.Coprime.gcd_mul_left_cancel _ this]
      _ ↔ (4 * a + 1).gcd (4 * b - 1) = 1 := by
        -- Use Euclidean algorithm.
        rw [show 4 * (a + b) = 4 * a + 1 + (4 * b - 1) by omega, Nat.gcd_self_add_left, Nat.gcd_comm]
  simp
  apply Iff.intro
  . -- First show that if 4a + 1 and 4b - 1 are coprime, and a + b ∣ 16ab + 1, then either b = 3a - 1 or a = 3b + 1.
    rintro ⟨ha, hb, h₁, h₂⟩
    -- Show that a + b ∣ 16a(a + b).
    have h₃ : a + b ∣ 16 * a * (a + b) := by
      apply Nat.dvd_mul_left
    -- Show that a + b ∣ (4a - 1)(4a + 1).
    have h₄ : a + b ∣ (4 * a + 1) * (4 * a - 1) := by
      rw [show (4 * a + 1) * (4 * a - 1) = 16 * a * (a + b) - (16 * a * b + 1) by rw [<-Nat.sq_sub_sq]; ring_nf; omega]
      apply Nat.dvd_sub (by nlinarith) h₃ h₂
    -- Show that a + b and 4a + 1 are coprime by using Euclidean algorithm for twice.
    -- Since a + b and 4a + 1 are coprime, we have a + b ∣ 4a - 1.
    rw [<-lm ha hb, <-Nat.coprime_iff_gcd_eq_one] at h₁
    rw [Nat.Coprime.dvd_mul_left h₁] at h₄
    -- We have a + b ≤ 4a - 1.
    have h₅ := Nat.le_of_dvd (by omega) h₄
    -- Let 4a - 1 = k(a + b).
    rw [dvd_iff_exists_eq_mul_left] at h₄
    obtain ⟨k, h₄⟩ := h₄
    -- Show that k is odd.
    have hk : k % 2 ≠ 0 := by
      by_contra!
      replace h₄ := congr_arg (· % 2) h₄
      simp [Nat.mul_mod, Nat.add_mod, this] at h₄
      omega
    -- Note that k < 4.
    have hk' : k < 4 := by
      -- Assume not, then it contradicts with 4a - 1 = k(a + b).
      by_contra!
      replace h₄ : 4 * a - 1 ≥ 4 * (a + b) := by
        nlinarith
      absurd h₄
      omega
    -- Since k is odd and k < 4, we have k = 1 or 3.
    replace hk' : k = 1 ∨ k = 3 := by
      omega
    cases' hk' with hk' hk'
    . -- Suppose k = 1.
      simp [hk'] at h₄
      -- We have b = 3a - 1.
      replace h₄ : b = 3 * a - 1 := by
        omega
      -- This corresponds to the first case of solution.
      left
      use a, ha, by rfl, h₄.symm
    . -- Suppose that k = 3.
      simp [hk'] at h₄
      -- We have a = 3b + 1.
      replace h₄ : a = 3 * b + 1 := by
        omega
      -- This corresponds to the second case of solution.
      right
      exact ⟨hb, h₄.symm⟩
  . -- Show that the solutions indeed satisfy the condition.
    rintro (h | h)
    . obtain ⟨a', ha, h', h₀⟩ := h
      subst a'
      refine ⟨?_, ?_, ?_, ?_⟩
      . -- First we have 0 < a.
        exact ha
      . -- We have 0 < b.
        omega
      . -- We have (4a + 1) and (4b - 1) coprime.
        rw [<-lm ha (by omega), <-h₀, show 4 * a + 1 = a + (3 * a - 1) + 2 by omega, Nat.gcd_self_add_right, Nat.gcd_comm, <-Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd (Nat.prime_two)]
        -- We have 2 ∤ 4a - 1.
        by_contra!
        omega
      . -- Show that a + b ∣ 16ab + 1.
        zify
        rw [<-h₀, Int.natCast_sub]
        push_cast
        ring_nf
        rw [show (1 - a * 16 + a ^ 2 * 48 : ℤ) = (-1 + a * 4) * (-1 + a * 12) by ring]
        apply Int.dvd_mul_right
        omega
    . obtain ⟨hb, h₀⟩ := h
      refine ⟨?_, ?_, ?_, ?_⟩
      . -- First we have 0 < a.
        omega
      . -- We have 0 < b.
        exact hb
      . -- We have (4a + 1) and (4b - 1) coprime.
        rw [<-lm (by omega) hb, <-h₀, show 3 * b + 1 + b = 4 * b + 1 by ring, show 4 * (3 * b + 1) + 1 = 3 * (4 * b + 1) + 2 by ring, Nat.gcd_mul_right_add_right, Nat.gcd_comm, <-Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd (Nat.prime_two)]
        -- We have 2 ∤ 4b + 1.
        by_contra!
        omega
      . -- Show that a + b ∣ 16ab + 1.
        rw [<-h₀]
        ring_nf
        rw [show 1 + b * 16 + b ^ 2 * 48 = (1 + b * 4) * (1 + b * 12) by ring]
        apply Nat.dvd_mul_right
