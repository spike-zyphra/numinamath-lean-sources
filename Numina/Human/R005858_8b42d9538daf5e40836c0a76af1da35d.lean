import Mathlib

/-let f(x) = x ^ 3 - 3x, compute the number of positive divisors of f(f(..f(5/2)))
where f is apllied 8 times -/
noncomputable def f: ℚ → ℚ := fun x => x ^ 3 - 3 * x
theorem algebra_610307: ⌊f^[8] (5/2)⌋.natAbs.divisors.card = 6562 := by
    have id: ∀ k: ℕ, f^[k] (5/2) = 2 ^ (3 ^ k) + 1 / (2 ^ (3 ^ k)) := by
        intro k
        induction' k with k hk
        . simp [f]
          linarith
        . rw [show f^[k + 1] (5/2) = f (f^[k] (5/2)) by simp [Function.iterate_succ_apply']]
          rw [hk]
          rw [f]
          clear hk
          field_simp
          ring
    have simplifier: ⌊f^[8] (5/2)⌋ = 2 ^ (3 ^ 8) := by
        specialize id 8
        rw [id]
        set b:= (1: ℚ) / (2 ^ (3 ^ 8)) with hb
        have hb2: b < 1 := by
            rw [hb]
            rw [div_lt_iff₀']
            . calc
                (1: ℚ) < 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (3 ^ 8) := by apply pow_le_pow_right₀; norm_num; norm_num
                _ = 2 ^ (3 ^ 8) * 1 := by rw[mul_one]
            . apply pow_pos
              norm_num
        rw [Int.floor_eq_iff]
        constructor
        . rw [hb]
          norm_num
        . calc
                2 ^ 3 ^ 8 + b < 2 ^ 3 ^ 8 + 1 := by linarith
                            _ = ↑(2 ^ 3 ^ 8 : ℤ) + 1 := by nth_rewrite 2[show (1: ℚ) = ↑(1: ℤ) by norm_num]; rw[←Int.cast_add];norm_num
    rw [simplifier]
    have l: (2 ^ 3 ^ 8: ℤ).natAbs = (2 ^ 3 ^ 8: ℕ) := by omega
    rw [l]
    rw [show 3 ^ 8 = 6561 by norm_num]
    have pp: Nat.Prime 2 := by norm_num
    rw [Nat.divisors_prime_pow pp]
    clear id simplifier l
    simp