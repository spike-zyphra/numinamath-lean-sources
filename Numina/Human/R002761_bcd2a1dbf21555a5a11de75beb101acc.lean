import Mathlib

/- if 0 < x, then numbers of digits of x > 0.  -/
lemma l_length_pos_of_pos {x:ℕ} (hx: 0 < x):
  0 < (Nat.digits 10 x).length := by
  refine List.length_pos.mpr ?_
  exact Nat.digits_ne_nil_iff_ne_zero.mpr hx.ne'

/-
93.3. Find all solutions of the system of equations

$$
\left\{\begin{aligned}
s(x)+s(y) & =x \\
x+y+s(z) & =z \\
s(x)+s(y)+s(z) & =y-4
\end{aligned}\right.
$$

where $x, y$, and $z$ are positive integers, and $s(x), s(y)$, and $s(z)$ are the numbers of digits in the decimal representations of $x, y$, and $z$, respectively.
-/
theorem number_theory_110168 {x y z: ℕ} (xpos: 0 < x)
  (ypos: 0 < y) (zpos: 0 < z) :
  ( (Nat.digits 10 x).length + (Nat.digits 10 y).length = x ∧
    x + y + (Nat.digits 10 z).length = z ∧
    (Nat.digits 10 x).length + (Nat.digits 10 y).length +
      (Nat.digits 10 z).length = y - 4 ) ↔
  (x = 2 ∧ y = 8 ∧ z = 12) := by

  constructor

  · rintro ⟨h1, h2, h3⟩
    have hx := l_length_pos_of_pos xpos
    have hy := l_length_pos_of_pos ypos
    have hz := l_length_pos_of_pos zpos
    -- from first equation, x ≥ 2.
    have xge: x ≥ 2 := by
      rw [← h1]
      linarith only [hx, hy]
    -- substract first equation from third equation:
    have h4: (Nat.digits 10 z).length = y - 4 - x := by
      have: (Nat.digits 10 z).length =
        (Nat.digits 10 x).length + (Nat.digits 10 y).length +
        (Nat.digits 10 z).length -
        ((Nat.digits 10 x).length + (Nat.digits 10 y).length) := by simp
      rw [this, h3, h1]
    -- then y-4-x > 0, y ≥ 5+x ≥ 7
    have yge: y ≥ 7 := by
      rw [h4] at hz
      clear * - xge hz
      omega
    -- substitute h4 into second equation, z = 2y-4
    have h5: z = 2*y - 4 := by
      rw [h4] at h2 hz
      clear h1 h3 hx hy h4 xge yge
      omega

    -- then digit length of z ≤ that of y + 1
    have digit_z: (Nat.digits 10 z).length ≤ (Nat.digits 10 y).length + 1 := by
      have hh1: 10^(Nat.digits 10 z).length ≤ 10 * z :=
        Nat.base_pow_length_digits_le' 8 z zpos.ne'
      have hh2: 10*z < 20*y := by
        rw [h5, Nat.mul_sub]
        omega
      have hh3: 20 * y < 10^(2 + (Nat.digits 10 y).length) := by
        have: y < 10^(Nat.digits 10 y).length :=
          Nat.lt_base_pow_length_digits'
        rw [pow_add]
        apply Nat.mul_lt_mul_of_lt_of_lt (by norm_num) this
      have := (lt_of_le_of_lt hh1 hh2).trans hh3
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at this
      clear * - this
      omega
    -- also, digit length x ≤ digit length y, since x ≤ y
    have digit_x: (Nat.digits 10 x).length ≤ (Nat.digits 10 y).length := by
      refine Nat.le_digits_len_le 10 x y ?_
      rw [h4] at hz
      clear * - hz
      omega
    -- then y-4 ≤ 3 digit length y + 1
    have digit_y: y - 4 ≤ 3 * (Nat.digits 10 y).length + 1 := by
      rw [← h3]
      linarith only [digit_z, digit_x]
    -- thus we solve digit length of y can only be 1 or 2.
    have: (Nat.digits 10 y).length ≤ 2 := by
      have hh1: 10^((Nat.digits 10 y).length - 1) ≤ y := by
        rw [Nat.digits_len _ _ (by norm_num) ypos.ne']
        simp only [add_tsub_cancel_right]
        exact Nat.pow_log_le_self 10 ypos.ne'
      have hh2: y ≤ 3 * (Nat.digits 10 y).length + 5 := by
        clear * - digit_y
        omega
      have hh3 {a: ℕ} (ha: a ≥ 3): 3*a + 5 < 10^(a-1) := by
        induction' a,ha using Nat.le_induction with a ha ih
        · norm_num
        · rw [show a+1-1 = a-1+1 by omega, pow_succ]
          have: (3*a+5)*10 < 10^(a-1)*10 := by
            exact Nat.mul_lt_mul_of_pos_right ih (by norm_num)
          refine lt_trans ?_ this
          linarith only [ha]
      by_contra!
      have hh := hh1.trans hh2
      absurd hh
      push_neg
      apply hh3 this
    obtain (hhy | hhy): (Nat.digits 10 y).length = 1 ∨
      (Nat.digits 10 y).length = 2 := by omega
    · -- digits length of y = 1, x must be 2.
      have xeq: x = 2 := by
        rw [hhy] at h1
        have hh1: 10^((Nat.digits 10 x).length - 1) ≤ x := by
          rw [Nat.digits_len _ _ (by norm_num) xpos.ne']
          simp only [add_tsub_cancel_right]
          exact Nat.pow_log_le_self 10 xpos.ne'
        rw [show (Nat.digits 10 x).length - 1 = x -2 by omega] at hh1
        have hh2 {a:ℕ} (ha: 0 < a): 10^a > a+2 := by
          induction' a,ha using Nat.le_induction with a ha ih
          · norm_num
          · rw [pow_succ]
            have: 10^a * 10 > (a+2) * 10 := by
              exact (Nat.mul_lt_mul_right (by norm_num)).mpr ih
            refine lt_trans ?_ this
            linarith only
        by_contra!
        replace: 0 < x-2 := by omega
        absurd hh1
        push_neg
        nth_rw 1 [show x = x-2+2 by omega]
        apply hh2 this
      -- and 7 ≤ y ≤ 8, y = 7 or 8.
      obtain (yeq | yeq): y = 7 ∨ y = 8 := by
        rw [hhy] at digit_y
        clear * - yge digit_y
        omega
      · -- x=2, y=7, digit length z = 1
        replace h4: (Nat.digits 10 z).length = 1 := by
          rw [h4, xeq, yeq]
        -- but we solve z = 10, contradiction
        rw [xeq, yeq, h4] at h2
        norm_num at h2
        norm_num [← h2] at h4
      · -- x=2, y=8, we solve z = 12, done.
        rw [xeq, h5, yeq]
        norm_num

    · -- digit length of y = 2 case.
      replace yge: y ≥ 10 := by
        have: y ≥ 10^(Nat.log 10 y) :=
          Nat.pow_log_le_self 10 ypos.ne'
        rw [Nat.digits_len _ _ (by norm_num) ypos.ne'] at hhy
        rwa [show Nat.log 10 y = 1 by omega, pow_one] at this
      rw [hhy] at digit_y h1
      -- y ≥ 10 , y ≤ 11, so y = 10 or 11
      obtain (yeq | yeq): y=10 ∨ y=11 := by
        clear * - digit_y yge
        omega
      · -- y = 10, z = 16
        norm_num [yeq] at h5
        -- we solve x = 4
        norm_num [h5, yeq] at h4
        replace h4: x = 4 := by omega
        -- contradicts to first equation
        norm_num [h4] at h1
      · -- y=11, z=18
        norm_num [yeq] at h5
        -- we splve x = 5
        norm_num [h5, yeq] at h4
        replace h4: x = 5 := by omega
        -- contradicts first equation.
        norm_num [h4] at h1

  · --verification
    rintro ⟨rfl, rfl, rfl⟩
    norm_num