import Mathlib
/- Find the number of triples $(a, b, c)$ of positive integers such that $a+a b+a b c=11$. -/
theorem algebra_609431 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a + a * b + a * b * c = 11} = {(1, 1, 9), (1, 2, 4), (1, 5, 1)}:= by
  ext ⟨a, b, c⟩
  constructor
  .
    intro h
    simp at h
    rcases h with ⟨ha, hb, hc, h1⟩
    -- Rearrange equation to factor out 'a'
    replace h1 : a * (1 + b + b * c) = 11:= by linarith
    -- Prove that 11 is prime
    have h2 : Nat.Prime 11:= by norm_num
    -- Since 'a' divides 11 and 11 is prime, a must be either 1 or 11
    have h3 : a ∣ 11:= by exact Dvd.intro (1 + b + b * c) h1
    replace h3 : a = 1 ∨ a = 11:= by exact (Nat.dvd_prime h2).mp h3
    -- Prove that a cannot be 11
    have h4 : a ≠ 11:= by
      by_contra H
      rw [H] at h1
      simp at h1
      have g1 : b * c > 0:= by positivity
      linarith
    -- Therefore a must be 1
    simp [h4] at h3
    subst a
    simp at h1
    -- After substituting a=1, simplify to b*(1+c) = 10
    replace h1 : b * (1 + c) = 2 * 5:= by linarith
    -- Prove that 5 is prime
    replace h4 : Nat.Prime 5:= by norm_num
    clear ha
    -- Since 5 divides b*(1+c), it must divide either b or (1+c)
    replace h2 : 5 ∣ b * (1 + c):= by exact Dvd.intro_left 2 (id (Eq.symm h1))
    replace h2 : 5 ∣ b ∨ 5 ∣ (1 + c):= by exact (Nat.Prime.dvd_mul h4).mp h2
    rcases h2 with h2 | h2
    .
      -- Case 1: 5 divides b
      replace h2 : ∃ b1 : ℕ, b = 5 * b1:= by exact h2
      rcases h2 with ⟨b1, hb1⟩
      rw [hb1] at h1
      replace h1 : b1 * (1 + c) = 2:= by linarith
      have h3 : b1 > 0:= by linarith
      have h4 : b1 * c > 0:= by positivity
      -- This leads to solution (1,5,1)
      replace h3 : b1 = 1:= by linarith
      subst b1
      replace h2 : c = 1:= by linarith
      simp at hb1
      subst b c
      simp
    .
      -- Case 2: 5 divides (1+c)
      replace h2 : ∃ c1 : ℕ, 1 + c = 5 * c1:= by exact h2
      rcases h2 with ⟨c1, hc1⟩
      rw [hc1] at h1
      replace h1 : b * c1 = 2:= by linarith
      -- Since b*c1 = 2, either b=1 and c1=2, or b=2 and c1=1
      have h2 : b = 1 ∨ c1 = 1:= by
        by_contra H
        simp at H
        rcases H with ⟨H1, H2⟩
        replace H1 : b ≥ 2:= by omega
        replace H2 : c1 ≥ 2:= by omega
        have H3 : b * c1 ≥ 2 * 2:= by exact Nat.mul_le_mul H1 H2
        linarith
      rcases h2 with h2 | h2
      .
        -- This leads to solution (1,1,9)
        subst b
        replace hc1 : c = 9:= by linarith
        subst c
        simp
      .
        -- This leads to solution (1,2,4)
        subst c1
        simp at h1
        replace hc1 : c = 4:= by linarith
        subst b c
        simp
  .
    -- Prove that each of the three claimed solutions satisfies the equation
    intro h
    simp at h
    rcases h with h | h | h
    all_goals
      simp
      rcases h with ⟨ha, hb, hc⟩
      subst a b c
      simp
