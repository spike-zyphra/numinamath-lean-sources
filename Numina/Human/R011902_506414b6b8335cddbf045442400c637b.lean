import Mathlib

theorem number_theory_301140 :
 { (a, b) : ℕ × ℕ | a.Prime ∧ b.Prime ∧ a^b * b^a = (2*a + b + 1) * (2*b + a + 1)}.ncard = 2 :=
by
  have : {(a, b) | Nat.Prime a ∧ Nat.Prime b ∧ a ^ b * b ^ a = (2 * a + b + 1) * (2 * b + a + 1)} = {(2,3), (3,2)} := by
    ext ⟨a,b⟩
    -- First we verify the answer is correct by checking the two cases:
    constructor; swap
    . intro h
      rcases h with (h|h)
      . simp at h
        rw [h.1, h.2]
        simp
        decide
      . simp at h
        rw [h.1, h.2]
        simp
        decide
    . simp
      intro ap bp eqn
      rcases em (Odd a ∧ Odd b) with (h|h)
      . -- If $a$ and $b$ are both odd,
        apply_fun (fun x => x % 2) at eqn
        -- then the left side of equation (1) $\\equiv 1 \\times 1 \\equiv 1(\\bmod 2)$,
        have lhs : a^b * b^a % 2 = 1 := by
          apply Nat.odd_iff.mp
          apply Nat.odd_mul.mpr; constructor
          . apply Odd.pow; tauto
          . apply Odd.pow; tauto
        -- the right side of equation (1) $\\equiv(2 \\times 1+1+1)(2 \\times 1+1+1)$ $\\equiv 0(\\bmod 2)$.
        have rhs : (2*a + b + 1) * (2*b + a + 1) % 2 = 0 := by
          apply Nat.even_iff.mp
          apply Nat.even_mul.mpr; left
          . rw [add_assoc]
            apply Nat.even_add.mpr; constructor
            . intro _
              apply Odd.add_one
              tauto
            . intro _
              apply even_two_mul
        -- Clearly, the left side is not congruent to the right side $(\\bmod 2)$, a contradiction.
        rw [lhs, rhs] at eqn
        simp at eqn
      . -- Therefore, at least one of $a$ and $b$ must be even.
        -- Since $a$ and $b$ are both prime numbers, so one of them must be $2$.
        have : a = 2 ∨ b = 2 := by
          have : ¬ Odd a ∨ ¬ Odd b := by tauto
          rw [Nat.not_odd_iff_even, Nat.not_odd_iff_even] at this
          rcases this with (h|h)
          . left
            exact (Nat.Prime.even_iff ap).mp h
          . right
            exact (Nat.Prime.even_iff bp).mp h
        rcases this with (h|h)
        . -- we assume $a=2$ first.
          rw [h] at eqn
          simp at eqn
          -- Then $2^{b} b^{2}=(b+5)(2 b+3)$.
          rw [show 4 + b + 1 = b + 5 by ring_nf, show 2*b + 2 + 1 = 2*b + 3 by ring_nf] at eqn
          -- Clearly, $b \\neq 2$, so $b \\geqslant 3$.
          have bu : b ≥ 3 := by
            have : b ≥ 2 := Nat.Prime.one_lt bp
            rcases em (b = 2) with (h|h)
            . -- Clearly, $b \\neq 2$,
              rw [h] at eqn
              simp at eqn
            . omega
          -- We can also show that b \lt 5.
          have bl : b < 5 := by
            -- We prove by contradiction.
            by_contra h
            push_neg at h
            -- So that we have, $$ 2^{b} b^{2} \\geqslant 2^{5} b^{2}=4 b \\times 8 b&gt;(b+5)(2 b+3) \\text {. } $$
            have : 2^b * b^2 > (b + 5) * (2 * b + 3) := by
              calc
                _ ≥ 2^5 * b^2 := by
                  apply Nat.mul_le_mul
                  refine Nat.pow_le_pow_right ?_ h
                  simp
                  simp
                _ = 4*b  * 8*b := by ring_nf
                _ > _ := by
                  ring_nf
                  have : 30 * b^2 > 15 + 13 * b := by
                    zify
                    have : (30 * b^2 - 13 * b : ℤ) > 15 := by
                      have : (30 * b^2 - 13 * b: ℤ) = (30 * b - 13) * b := by ring_nf
                      rw [this, show (15 : ℤ) = 3 * 5 by simp]
                      apply Int.mul_lt_mul <;> try simp
                      . have : (30 * b : ℤ) > 16 := by
                          calc
                            _ ≥ (30 * 5 : ℤ) := by
                              apply Int.mul_le_mul <;> simp
                              assumption
                            _ > _ := by simp
                        omega
                      . assumption
                      . calc
                          _ ≤ (30 * 5 : ℤ) := by simp
                          _ ≤ _ := by
                            apply Int.mul_le_mul <;> simp
                            assumption
                    omega
                  have : 30 * b^2 + 2 * b^2 > 15 + 13 * b + 2 * b^2 := by linarith
                  ring_nf at this
                  exact this
            omega
          interval_cases b
          . tauto
          . exfalso
            apply show ¬ Nat.Prime 4 by decide
            exact bp
        . -- This case is similar to the previous one.
          rw [h] at eqn
          simp at eqn
          rw [show 4 + a + 1 = a + 5 by ring_nf, show 2*a + 2 + 1 = 2*a + 3 by ring_nf] at eqn
          have au : a ≥ 3 := by
            have : a ≥ 2 := Nat.Prime.one_lt ap
            rcases em (a = 2) with (h|h)
            . rw [h] at eqn
              simp at eqn
            . omega
          have al : a < 5 := by
            by_contra h
            push_neg at h
            have : 2^a * a^2 > (a + 5) * (2 * a + 3) := by
              calc
                _ ≥ 2^5 * a^2 := by
                  apply Nat.mul_le_mul
                  refine Nat.pow_le_pow_right ?_ h
                  simp
                  simp
                _ = 4*a  * 8*a := by ring_nf
                _ > _ := by
                  ring_nf
                  have : 30 * a^2 > 15 + 13 * a := by
                    zify
                    have : (30 * a^2 - 13 * a : ℤ) > 15 := by
                      have : (30 * a^2 - 13 * a: ℤ) = (30 * a - 13) * a := by ring_nf
                      rw [this, show (15 : ℤ) = 3 * 5 by simp]
                      apply Int.mul_lt_mul <;> try simp
                      . have : (30 * a : ℤ) > 16 := by
                          calc
                            _ ≥ (30 * 5 : ℤ) := by
                              apply Int.mul_le_mul <;> simp
                              assumption
                            _ > _ := by simp
                        omega
                      . assumption
                      . calc
                          _ ≤ (30 * 5 : ℤ) := by simp
                          _ ≤ _ := by
                            apply Int.mul_le_mul <;> simp
                            assumption
                    omega
                  have : 30 * a^2 + 2 * a^2 > 15 + 13 * a + 2 * a^2 := by linarith
                  ring_nf at this
                  exact this
            rw [mul_comm, mul_comm (a + 5)] at this
            omega
          interval_cases a
          . tauto
          . exfalso
            apply show ¬ Nat.Prime 4 by decide
            exact ap
  rw [this]
  simp
