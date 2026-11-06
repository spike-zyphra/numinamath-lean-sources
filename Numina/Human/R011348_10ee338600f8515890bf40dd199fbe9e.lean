import Mathlib

/-
What is the remainder of the Euclidean division of $2022^{2022^{2022}}$ by 11?

Answer is 5.
-/
theorem number_theory_116412 : 2022 ^ 2022 ^ 2022 % 11 = 5 := by

  -- We first show that if $n$ is a natural number that leaves a
  -- remainder of $2$ when divided by $4$, then $2022^n$ leaves a
  -- remainder of $4$ when divided by $10$.
  have h₁ (n : ℕ) (hn : n % 4 = 2) : 2022 ^ n % 10 = 4 := by
    -- We show by induction on $k$ that
    -- $2022^{4k+2}$ leaves a remainder of $4$ when divided by $10$.
    have h₂ : ∀ k, (2022 ^ (4 * k + 2)) % 10 = 4 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h4 : 4 * (k + 1) + 2 = 4 * k + 2 + 4 := by omega
        rw [h4]
        have h5 : (2022 ^ (4 * k + 2 + 4)) % 10 = (2022 ^ (4 * k + 2) * 2022 ^ 4) % 10 := by
          simp [Nat.pow_add]
        rw [h5]
        have h6 : (2022 ^ (4 * k + 2) * 2022 ^ 4) % 10 = (2022 ^ (4 * k + 2) % 10) * (2022 ^ 4 % 10) % 10 := by
          simp [Nat.mul_mod]
        rw [h6]
        have h7 : 2022 ^ (4 * k + 2) % 10 = 4 := ih
        have h8 : 2022 ^ 4 % 10 = 6 := by
          norm_num
        rw [h7, h8]
    simp [Nat.ModEq] at hn ⊢
    have : ∃ k, n = 4 * k + 2 := by
      refine' ⟨n / 4, by omega⟩
    rcases this with ⟨k, rfl⟩
    have hk : (2022 ^ (4 * k + 2)) % 10 = 4 := h₂ k
    exact hk

  -- It follows that there exists $k$ such that $2022^{2022} = 10k + 4$.
  have : ∃ k, 2022 ^ 2022 = 10 * k + 4 := by
    use (2022 ^ 2022 / 10)
    have : 2022 % 4 = 2 := by decide
    rw [← h₁ 2022 this]
    have (a q : ℕ) : a = q * (a / q) + a % q := by exact Eq.symm (Nat.div_add_mod a q)
    apply this
  obtain ⟨ k, hk ⟩ := this

  -- We prove Fermat's Little Theorem: That if $a$ and $p$ are natural numbers
  -- and $p$ is prime and $a$ and $p$ are coprime, then $a^{p-1}$ is congruent to 1
  -- modulo $p$.
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
    simp at fermat ⊢
    exact fermat

  -- Since $11$ is prime and $2022$ and $11$ are coprime,
  -- It follows from Feramt's Little Theorem that $2022 ^ 10$ leaves
  -- a remainder of 1 when divided by 11.
  have h₂ : 2022 ^ 10 % 11 = 1 := by
    suffices 2022 ^ 10 ≡ 1 [MOD 11] by exact this
    apply fermatLittle
    all_goals decide

  -- Then $2022^{2022^2022} = 2022^{10k + 4} = (2022^10)^k \cdot 2022^4$ which
  -- leaves a remainder equals the remainder of $2022^4$ when divided by 11, which
  -- which is $5$ by a simple calculation.
  calc
    _ = 2022 ^ (10 * k + 4) % 11 := by rw [hk]
    _ = 2022 ^ (10 * k) * 2022 ^ 4 % 11 := by rw [pow_add]
    _ = (2022 ^ (10 * k) % 11) * 2022 ^ 4 % 11 := by rw [← Nat.mod_mul_mod]
    _ = (2022 ^ 10) ^ k % 11 * 2022 ^ 4 % 11 := by rw [pow_mul]
    _ = (2022 ^ 10 % 11) ^ k % 11 * 2022 ^ 4 % 11 := by rw [Nat.pow_mod]
    _ = 1 ^ k % 11 * 2022 ^ 4 % 11 := by rw [h₂]
    _ = 1 % 11 * 2022 ^ 4 % 11 := by rw [one_pow]
    _ = 1 * 2022 ^ 4 % 11 := by have : 1 % 11 = 1 := by decide
                                rw [this]
    _ = 2022 ^ 4 % 11 := by rw [one_mul]
    _ = _ := by decide
