import Mathlib

/- 14.1.21 ** Let $a$ and $b$ be two different integers greater than 1, and $b^{2}+a-1$ divides $a^{2}+b-1$. Prove: $b^{2}+a-1$ has at least two different prime factors. -/
theorem number_theory_260083 {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hdiv : b^2 + a - 1 ∣ a^2 + b - 1) (hne : a ≠ b) :
    (b^2 + a - 1).primeFactors.card ≥ 2 := by
  -- prove some auxiliary inequalities which help to switch between ℕ and ℤ
  have h1 : 1 ≤ b ^ 2 + a := by omega
  have h2 : 1 ≤ a ^ 2 + b := by omega
  have h3 : 1 ≤ b ^ 2 + b := by omega
  have h4 : 1 ≤ b ^ 2 := calc
    1 = 1 ^ 2 := by norm_num
    _ ≤ b ^ 2 := by apply Nat.pow_le_pow_left (by omega)
  -- show that b < a
  have hba : b < a := by
    -- from b ^ 2 + a - 1 ∣ a ^ 2 + b - 1 we get b ^ 2 + a - 1 ≤ a ^ 2 + b - 1
    have ineq := Nat.le_of_dvd (by omega) hdiv
    zify [h1, h2] at ineq ⊢
    -- we obtain 0 ≤ (a - b) * (b + a - 1)
    replace ineq : 0 ≤ ((a : ℤ) - b) * (b + a - 1) := by linarith
    rw [mul_nonneg_iff] at ineq
    -- it follows that b < a because 1 < a and 1 < b
    omega
  -- assume that b ^ 2 + a - 1 has less than 2 prime factors
  by_contra! h
  interval_cases h : (b ^ 2 + a - 1).primeFactors.card <;> clear h
  -- if b ^ 2 + a - 1 has no prime factors then b ^ 2 + a - 1 = 0 or 1
  -- which is impossible since a > 1 and b > 1
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h
    omega
  -- suppose that b ^ 2 + a - 1 = p ^ k for some prime p and k > 0
  rw [←isPrimePow_iff_card_primeFactors_eq_one] at h
  have ⟨p, k, hp, hk1, heq⟩ := h
  -- show that p ^ k divides b * (b - 1) * (b ^ 2 + b - 1)
  replace hdiv : p ^ k ∣ b * (b - 1) * (b ^ 2 + b - 1) := by
    have eq : b * (b - 1) * (b ^ 2 + b - 1) + a * (b ^ 2 + a - 1) = a ^ 2 + b - 1 + (b ^ 2 - 1) * (b ^ 2 + a - 1) := by
      zify [h1, h2, h3, h4, hb]
      ring
    -- it is enough to show that p ^ k divides b * (b - 1) * (b ^ 2 + b - 1) + a * (b ^ 2 + a - 1)
    suffices p ^ k ∣ b * (b - 1) * (b ^ 2 + b - 1) + a * (b ^ 2 + a - 1) by
      apply (Nat.dvd_add_iff_left _).mpr this
      use a
      rw [heq, mul_comm]
    -- we have b * (b - 1) * (b ^ 2 + b - 1) + a * (b ^ 2 + a - 1)
    --       = (a ^ 2 + b - 1) + (b ^ 2 - 1) * (b ^ 2 + a - 1)
    --       = (a ^ 2 + b - 1) + (b ^ 2 - 1) * p ^ k
    -- we also know that b ^ 2 + a - 1 = p ^ k divides a ^ 2 + a - 1
    rw [eq]
    apply Nat.dvd_add (heq ▸ hdiv)
    use b ^ 2 - 1
    rw [heq, mul_comm]
  -- show that b and b - 1 are coprime
  have hp1 : b.Coprime (b - 1) := by
    apply IsCoprime.nat_coprime
    push_cast [hb]
    use 1, -1
    ring
  -- show that b and b ^ 2 + b - 1 are coprime
  have hp2 : b.Coprime (b ^ 2 + b - 1) := by
    apply IsCoprime.nat_coprime
    push_cast [h3]
    use b + 1, -1
    ring
  -- show that b - 1 and b ^ 2 + b - 1 are coprime
  have hp3 : (b - 1).Coprime (b ^ 2 + b - 1) := by
    apply IsCoprime.nat_coprime
    push_cast [h3, hb]
    use -b - 2, 1
    ring
  -- from p ^ k ∣ b * (b - 1) * (b ^ 2 + b - 1) we get that
  -- either p ^ k ∣ b or p ^ k ∣ b - 1 or p ^ k ∣ b ^ 2 + b - 1
  rw [mul_assoc, Nat.Coprime.isPrimePow_dvd_mul (Nat.Coprime.mul_right hp1 hp2) (heq ▸ h)] at hdiv
  rw [Nat.Coprime.isPrimePow_dvd_mul hp3 (heq ▸ h)] at hdiv
  -- consider all 3 cases and show that p ^ k ∣ x implies p ^ k ≤ x
  -- at the same time we have p ^ k > b, p ^ k > b - 1, and p ^ k > b ^ 2 + b - 1, a contradiction
  rcases hdiv with h | h | h
  all_goals {
    apply Nat.le_of_dvd (by omega) at h;
    contrapose! h
    omega
  }