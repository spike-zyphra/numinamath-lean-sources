import Mathlib

/- Given that $a, b, c$ are positive integers satisfying

$$
a+b+c=\operatorname{gcd}(a, b)+\operatorname{gcd}(b, c)+\operatorname{gcd}(c, a)+120
$$

determine the maximum possible value of $a$.-/
theorem number_theory_611051 :
    IsGreatest {a : ℕ | 0 < a ∧ ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ a + b + c = Nat.gcd a b + Nat.gcd b c + Nat.gcd c a + 120} 240 := by
  -- Simplify the goal into two parts.
  simp only [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- Prove that 240 is possible.
    norm_num
    -- A possible value of (a, b, c) is (240, 120, 120).
    use 120, by norm_num, 120
    norm_num
  . -- Show that it could not be anything greater.
    intro a h
    obtain ⟨ha, b, c, hb, hc, h₀⟩ := h
    -- WLOG, assume that a > b.
    wlog h₁ : a > b
    . -- Show that other cases are similar.
      by_cases h₂ : b > c
      . -- Suppose that a ≤ b but b > c.
        -- Use the result of the wlog with (b, c, a) instead of (a, b, c).
        specialize this hb c a hc ha (by linarith only [h₀]) h₂
        -- We have a ≤ b ≤ 240.
        simp at h₁
        exact h₁.trans this
      . -- Suppose that a ≤ b ≤ c.
        -- Note that they cannot be all equal, so a < c.
        have h₃ : a < c := by
          by_contra! h₃
          replace h₃ : a = c := by
            linarith
          replace h₂ : b = c := by
            linarith
          -- Substitute c = a = b into the original equation, we got a contradiction.
          simp [h₃, h₂] at h₀
        -- Use the result of the wlog with (c, a, b) instead of (a, b, c).
        specialize this hc a b ha hb (by linarith only [h₀]) h₃
        -- We have a ≤ c ≤ 240.
        simp at h₁ h₂
        exact (h₁.trans h₂).trans this
    . -- Now suppose that a > b.
      -- We have a ≤ gcd (a, b) + 120.
      have h₂ : a ≤ Nat.gcd a b + 120 := by
        suffices a + b + c ≤ Nat.gcd a b + b + c + 120 by
          linarith
        calc
          a + b + c = Nat.gcd a b + Nat.gcd b c + Nat.gcd c a + 120 := h₀
          _ ≤ Nat.gcd a b + b + c + 120 := by
            -- Since gcd (b, c) ≤ b and gcd (c, a) ≤ c, we get the desired result.
            iterate 3 apply Nat.add_le_add
            . rfl
            . exact Nat.gcd_le_left _ hb
            . exact Nat.gcd_le_left _ hc
            . rfl
      -- Show that a ≥ 2gcd (a, b).
      have h₃ : a ≥ 2 * Nat.gcd a b := by
        -- We have a = k * gcd (a, b) for some k.
        have : Nat.gcd a b ∣ a := by
          apply Nat.gcd_dvd_left
        rw [dvd_iff_exists_eq_mul_left] at this
        obtain ⟨k, hk⟩ := this
        -- We have k ≠ 1.
        have hk' : k ≠ 1 := by
          by_contra!
          -- Assume on the contrary that k = 1, then a = gcd (a, b).
          simp [this] at hk
          symm at hk
          -- We get a ∣ b, so a ≤ b, contradiction.
          rw [<-Nat.gcd_eq_left_iff_dvd] at hk
          apply Nat.le_of_dvd hb at hk
          omega
        -- We also have k ≠ 0 for obvious reasons.
        have hk'' : k ≠ 0 := by
          by_contra!
          simp [this] at hk
          omega
        -- So k ≥ 2 and the result is clear.
        nth_rw 1 [hk, ge_iff_le]
        apply Nat.mul_le_mul_right
        omega
      -- We have a ≤ 240 by combining the above results.
      omega

