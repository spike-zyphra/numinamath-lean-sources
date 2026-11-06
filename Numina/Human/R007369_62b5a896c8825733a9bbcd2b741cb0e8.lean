import Mathlib

/- Trouver toutes les paires (m,n) d'entiers strictement positifs telles que

$$
\mathrm{m}!+\mathrm{n}!=\mathrm{m}^{\mathrm{n}}
$$

Remarque. Pour tout entier $n$, on rappelle que $n$ ! désigne l'entier $1 \times 2 \times 3 \times \cdots \times n$. -/
theorem number_theory_605553 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ Nat.factorial m + Nat.factorial n = m ^ n} = {(2, 2), (2, 3)} := by
  ext ⟨m, n⟩
  constructor
  . -- Show that the condition implies that (m, n) = (2, 2) or (2, 3).
    rintro ⟨hm, hn, h₀⟩
    -- Break the cases into two cases: m ≤ n and m > n.
    by_cases h₁ : m ≤ n
    . -- Suppose m ≤ n.
      by_cases h₂ : m = 1
      . -- Consider the cases m = 1.
          simp [h₂] at h₀
          linarith [Nat.factorial_pos n]
      . -- Consider the case m ≥ 2.
        have h₃ := Nat.factorial_dvd_factorial h₁
        -- We have m - 1 ∣ mⁿ.
        have h₄ : m - 1 ∣ m ^ n := by
          rw [<-h₀]
          apply Nat.dvd_add
          <;> exact Nat.dvd_factorial (by omega) (by omega)
        -- However, m - 1 and mⁿ are coprime.
        have h₅ : Nat.Coprime (m - 1) (m ^ n) := by
          apply Nat.Coprime.pow_right
          rw [Nat.coprime_self_sub_left (by omega)]
          simp
        -- We get m = 2.
        have h₆ : m = 2 := by
          have := Nat.Coprime.eq_one_of_dvd h₅ h₄
          omega
        subst m
        -- Assume on the contrary that (m, n) ∉ {(2, 2), (2, 3)}, then n ≥ 4.
        by_contra!
        simp at this
        -- The left-hand side of the equation is not divisble by 4 but the right hand side is.
        have h₃ : 4 ∣ 2 ^ n := by
          calc
            _ = 2 ^ 2 := by norm_num
            _ ∣ 2 ^ n := by
              apply Nat.pow_dvd_pow _ h₁
        replace h₁ : n ≥ 4 := by
          omega
        -- Since 4 ∣ n!, we have 4 ∣ 2, which is absurd.
        rw [<-h₀, <-Nat.dvd_add_iff_left (Nat.dvd_factorial (by norm_num) h₁)] at h₃
        norm_num at h₃
    . -- Suppose n < m.
      push_neg at h₁
      by_cases h₂ : n = 1
      . -- Suppose n = 1.
        simp [h₂] at h₀
        linarith [Nat.self_le_factorial m]
      . -- Suppose n ≥ 2.
        have h₃ := Nat.factorial_dvd_factorial (show n ≤ m - 1 by omega)
        -- Let k = (m - 1)! / n!.
        obtain ⟨k, h₃⟩ := h₃
        -- We have 1 + mk ∣ mⁿ.
        have h₄ : 1 + m * k ∣ m ^ n := by
          rw [<-h₀, <-Nat.mul_factorial_pred (by omega), h₃, mul_comm _ (Nat.factorial n * k), mul_assoc, <-Nat.mul_succ, show (k * m).succ = 1 + m * k by simp; ac_rfl]
          apply Nat.dvd_mul_left
        -- However, 1 + mk and mⁿ are coprime.
        have h₅ : Nat.Coprime (1 + m * k) (m ^ n) := by
          apply Nat.Coprime.pow_right
          simp [Nat.coprime_iff_gcd_eq_one]
        -- We get 1 + mk = 1, which is absurd.
        have h₆ := Nat.Coprime.eq_one_of_dvd h₅ h₄
        simp [hm.ne'] at h₆
        simp [h₆] at h₃
        linarith [Nat.factorial_pos (m - 1)]
  . -- Show that (m, n) = (2, 2) or (2, 3) satisfies the condition.
    rintro (⟨hm, hn⟩ | ⟨hm, hn⟩)
    . -- Case (m, n) = (2, 2).
      norm_num
    . -- Case (m, n) = (2, 3).
      decide