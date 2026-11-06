import Mathlib

/- 58. Given natural numbers $a, b$ and $c \geqslant b$. Prove that $a^{b}(a+b)^{c}>c^{b} a^{c}$. -/
theorem inequalities_183895 (a b c : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : b ≤ c) : a^b * (a + b)^c > c^b * a^c := by

      -- We'll start by proving special cases
      -- b = c is easy
      by_cases h₃' : b = c
      · subst h₃'
        simp only [gt_iff_lt]
        rw [mul_comm]
        refine (Nat.mul_lt_mul_left ?_).mpr ?_
        positivity
        convert_to (0 + b) ^ b < (a + b) ^ b
        rw [zero_add]
        refine Nat.pow_lt_pow_left ?_ ?_
        omega
        omega

      -- Then we have that b < c
      replace h₃' : b < c := Nat.lt_of_le_of_ne h₃ h₃'

      -- Simplify the expression
      rw [←Nat.pow_sub_mul_pow a h₃, ←mul_assoc, mul_comm]
      suffices h : c ^ b * a ^ (c - b) < (a + b) ^ c
      · refine (Nat.mul_lt_mul_right ?_).mpr h
        positivity

      -- We prove b = 1 as a special case
      by_cases hh : b = 1
      · subst hh
        simp only [pow_one]
        -- We prove by induction on c
        induction' c, h₃' using Nat.le_induction with p hc2 hc3
        -- We have 2 ≤ c and that c = 2 is true
        · simp only [Nat.add_one_sub_one, pow_one, gt_iff_lt]
          rw [pow_two]
          ring_nf
          omega
        -- Assume that c = p is true, then we prove c = p + 1
        · have hyp := hc3 (by omega) (by omega)
          rw [add_mul, one_mul]
          calc p * a ^ (p + 1 - 1) + a ^ (p + 1 - 1)
          -- Reorganize LHS
          _ = p * a ^ (p - 1) * a + a ^ p := by
            simp only [add_tsub_cancel_right, add_left_inj]
            rw [mul_assoc]
            congr
            exact Eq.symm <| Nat.pow_pred_mul <| Nat.zero_lt_of_lt hc2
          _ = a * (p * a ^ (p - 1)) + a ^ p := by
            rw [mul_comm]
          -- Use induction hypethesis
          _ < a * ((a + 1) ^ p) + a ^ p := by
            refine Nat.add_lt_add_right ?_ _
            exact Nat.mul_lt_mul_of_pos_left hyp h₀
          -- which is still less than RHS
          _ < a * (a + 1) ^ p + (a + 1) ^ p := by
            refine Nat.add_lt_add_left ?_ (a * (a + 1) ^ p)
            apply Nat.pow_left_strictMono <;> omega
          _ = (a + 1) ^ p * a + (a + 1) ^ p := by
            rw [mul_comm]

      have b_two : 1 < b := by omega

      -- We use the binomial theorem
      rw [Commute.add_pow <| Commute.all a b]

      -- Then we chain inequalities
      · calc c ^ b * a ^ (c - b)
        _ < a ^ (c-b) * b ^ b * c.choose b := by
          -- We express it as an inequality with factorials
          rw [mul_comm, mul_assoc]
          refine (Nat.mul_lt_mul_left (by positivity)).mpr ?_
          rw [Nat.choose_eq_factorial_div_factorial h₃]
          have b_pos : 0 < b.factorial := Nat.factorial_pos b
          refine (Nat.mul_lt_mul_right b_pos).mp ?_
          convert_to c ^ b * b.factorial < b ^ b * (c.factorial / (c - b).factorial)
          · rw [mul_assoc]
            refine (Nat.mul_left_cancel_iff ?_).mpr ?_
            · positivity
            rw [mul_comm, ←Nat.mul_div_assoc, Nat.mul_div_mul_left]
            · positivity
            exact Nat.factorial_mul_factorial_dvd_factorial h₃

          -- Then we express it as a product less than another product, over the same range
          rw [←Nat.descFactorial_eq_div h₃, Nat.descFactorial_eq_prod_range, ←Nat.one_ascFactorial,
            Nat.ascFactorial_eq_prod_range, Finset.pow_eq_prod_const, Finset.pow_eq_prod_const,
            ←Finset.prod_mul_distrib, ←Finset.prod_mul_distrib, ←Finset.prod_range_reflect]
          convert_to ∏ k ∈ Finset.range b, c * (b - k) < ∏ k ∈ Finset.range b, b * (c - k)
          · refine Finset.prod_congr rfl ?_
            intro x xh
            simp only [Finset.mem_range] at xh
            simp only [mul_eq_mul_left_iff]
            omega
          -- Then to show that one side is less than the other, we show that each LHS term
          -- is less than or equal to each RHS term and larger than 0, and that there's a LHS term that is less than it's RHS term.
          apply Finset.prod_lt_prod
          · simp only [Finset.mem_range, h₂, mul_pos_iff_of_pos_left, tsub_pos_iff_lt, imp_self,
              implies_true]
          · simp only [Finset.mem_range]
            intro i ih
            rw [Nat.mul_sub, Nat.mul_sub, mul_comm]
            refine Nat.sub_le_sub_left ?_ (b * c)
            exact Nat.mul_le_mul_right i h₃

          -- When k = 1, LHS term is less than RHS term.
          · refine ⟨1, ?_⟩
            simp only [Finset.mem_range, b_two, true_and]
            rw [Nat.mul_sub, Nat.mul_sub, mul_comm, mul_one, mul_one]
            -- We use that 2 ≤ b
            refine Nat.sub_lt_sub_left ?_ h₃'
            exact lt_mul_of_one_lt_of_lt' b_two h₃'

        -- Simple rewrites
        _ = a ^ (c-b) * b ^ (c - (c-b)) * c.choose (c-b)
          := by rw [Nat.choose_symm h₃, (Nat.sub_sub_self h₃)]

        -- We only used one term of the binomial expansion
        _ = ∑ x ∈ {c-b}, a ^ x * b ^ (c - x) * c.choose x
          := by simp only [Finset.sum_singleton]
        _ ≤ ∑ x ∈ Finset.range (c + 1), a ^ x * b ^ (c - x) * c.choose x := by
          refine Finset.sum_le_sum_of_ne_zero ?_
          intro aa bb cc
          simp only [Finset.mem_range]
          simp only [Finset.mem_singleton] at bb
          rw [bb]
          omega