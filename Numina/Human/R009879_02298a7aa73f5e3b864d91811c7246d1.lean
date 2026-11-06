import Mathlib

/- Find the largest negative integer $x$ which satisfies the congruence $34x+6\equiv 2\pmod {20}$. -/
theorem number_theory_14632:
  IsGreatest {x:ℤ | x < 0 ∧ 34 * x + 6 ≡ 2 [ZMOD 20]} (-6) := by
  -- simplify the congruence
  have h1: ∀x:ℤ, 34 * x + 6 ≡ 2 [ZMOD 20] → x ≡ (-6) [ZMOD 10] := by
    intro x ht1
    -- 34x+6 ≡ 2 [mod 20], so 14x+6 ≡ 2 [mod 20]
    have ht2:14*x + 6 ≡ 2 [ZMOD 20] := by
      have tt1: 14*x+6 = (34*x+6) + 20*(-x) := by ring
      rw [tt1]
      apply Int.modEq_add_fac (-x) ht1
    -- 14x ≡ 2-6 [mod 20] ≡ -4 [mod 20] ≡ 16 [mod 20]
    have ht3: 14*x ≡ 16 [ZMOD 20] := by
      have tt1: 14*x ≡ 2-6 [ZMOD 20] := by
        exact Int.ModEq.add_right_cancel' 6 ht2
      simp at tt1
      apply tt1
    -- 14x ≡ 16 [mod 20], so 7x ≡ 8 [mod 10]
    have ht4: 7*x ≡ 8 [ZMOD 10] := by
      have tt1: 0 < (20:ℤ) := by norm_num
      have tt2: (7*x)*2 ≡ 8*2 [ZMOD 20] := by
        ring_nf; rw [mul_comm x 14]; apply ht3
      have tt3 := Int.ModEq.cancel_right_div_gcd tt1 tt2
      norm_num at tt3
      apply tt3
    -- 7x ≡ 8 [mod 10], so 21x ≡ 3*8 = 24 [mod 10]
    have ht5: 21*x ≡ 24 [ZMOD 10] := by
      have tt1: 21*x = 3*(7*x) := by ring
      have tt2: (24:ℤ) = 3*8 := by ring
      rw [tt1, tt2]
      exact Int.ModEq.mul_left 3 ht4
    -- 21x ≡ x [mod 10]
    have ht6: 21*x ≡ x [ZMOD 10] := by
      have: 21*x = x + 10*(2*x) := by ring
      rw [this]
      exact Int.modEq_add_fac_self
    -- and 24 ≡ -6 [mod 10]
    exact Int.ModEq.trans (id (Int.ModEq.symm ht6)) ht5
  -- now we can solve the problem.
  rw [IsGreatest, upperBounds]; simp
  constructor
  --verify -6 satisfy the condition.
  · rfl
  -- show any negative integer satisfy the mod equation ≤ -6
  · intro x hx eqx1
    have eqx2 := h1 x eqx1
    have eqx3 := Int.ModEq.dvd eqx2
    rcases eqx3 with ⟨d,hd⟩
    -- 10 ∣ -6-x, so 10 ∣ x+6. and x is negative integer, so x can only be -6, -16, -26, ...    and all of these ≤ -6.
    omega