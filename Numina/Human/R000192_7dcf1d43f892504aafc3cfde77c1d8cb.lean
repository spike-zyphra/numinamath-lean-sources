import Mathlib

/-Find all integer solutions  $(a,b)$  of the equation \[ (a+b+3)^2 + 2ab = 3ab(a+2)(b+2)\]-/
theorem number_theory_8524 : ∀ (a b : ℤ), (a + b + 3) ^ 2 + 2 * a * b =
    3 * a * b * (a + 2) * (b + 2) ↔ (a, b) = (-3, 0) ∨ (a, b) = (-3, -3) ∨
    (a, b) = (-2, 1) ∨ (a, b) = (1, -2) ∨ (a, b) = (0, -3) ∨ (a, b) = (1, 1)
    ∨ (a, b) = (-1, -1) := by
  intro a b; constructor
  -- Prove that we have the following bounds on $a$ or $b$
  · intro heq; have aux : (a + 1) ^ 2 < 5 ∨ (b + 1) ^ 2 < 5 := by
    -- Rewrite the left-hand side
      have r1 : (a + b + 3) ^ 2 + 2 * a * b =
      (a + 1) ^ 2 + (b + 1) ^ 2 + 4 * (a + 1) * (b + 1) + 3 := by ring
    -- Rewrite the right-hand side
      have r2 : 3 * a * b * (a + 2) * (b + 2) =
      3 * (a + 1) ^ 2 * (b + 1) ^ 2 - 3 * ((a + 1) ^ 2 + (b + 1) ^ 2) + 3 := by ring
      rw [r1, r2] at heq
    -- Apply arithmetic mean-geometric mean inequality on the left-hand side
      have r3 : (a + 1) ^ 2 + (b + 1) ^ 2 + 4 * (a + 1) * (b + 1) + 3 ≤
      3 * ((a + 1) ^ 2 + (b + 1) ^ 2) + 3 := by
        nth_rw 2 [show (3:ℤ)=1+2 by norm_num]; rw [add_mul, one_mul]
        simp; rw [show (4:ℤ)=2*2 by norm_num, mul_assoc, mul_assoc]
        nth_rw 2 [← mul_assoc]; simp; apply two_mul_le_add_pow_two
  -- Rewrite r3 by using assumptions
      rw [heq] at r3; simp at r3
      rw [← add_mul, show (3:ℤ)+3=3*2 by norm_num] at r3
      rw [mul_assoc, mul_assoc] at r3; simp at r3
      rw [← zero_add (2 * ((a + 1) ^ 2 + (b + 1) ^ 2)), Int.le_add_iff_sub_le] at r3
    -- Rewrite the left-hand side as a product
      have r4 : (a + 1) ^ 2 * (b + 1) ^ 2 - 2 * ((a + 1) ^ 2 + (b + 1) ^ 2) =
      ((a + 1) ^ 2 - 2)*((b + 1) ^ 2 - 2) - 4 := by ring
      rw [r4, sub_le_iff_le_add, zero_add] at r3
    -- Prove by contradiction
      by_contra h'; push_neg at h'
      rcases h' with ⟨h'l, h'r⟩
      have r6 : 3 ≤ (a + 1) ^ 2 - 2 := by linarith
      have r7 : 3 ≤ (b + 1) ^ 2 - 2 := by linarith
      have r8 : 9 ≤ ((a + 1) ^ 2 - 2) * ((b + 1) ^ 2 - 2) := by
        rw [show (9:ℤ)=3*3 by norm_num]; apply mul_le_mul
        assumption; assumption; norm_num; linarith
      linarith
  -- Split to two cases according to `aux` and solve each case separately
    rcases aux with h1 | h1
    · replace h1 : (a + 1) ^ 2 < 3 ^ 2 := by omega
      rw [sq_lt_sq] at h1; norm_num at h1
      rw [abs_lt] at h1; rcases h1 with ⟨agt, alt⟩
      replace agt : -4 < a := by linarith only [agt]
      replace alt : a < 2 := by linarith only [alt]
    -- In the first case, we have $-4<a$ and $a<2$, so it is easy to find $b$ from the equation.
      interval_cases a; all_goals rw [← sub_eq_zero] at heq
      all_goals ring_nf at heq
      · simp [show -(b * 24) - b ^ 2 * 8 = -8*b*(b+3) by ring] at heq
        rcases heq with h|h; simp [h]
        rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
      · simp [show (1 - b * 2 + b ^ 2) = (b-1)^ 2 by ring] at heq
        rw [sub_eq_zero] at heq; simp [heq]
      · simp [show 4 + b * 8 + b ^ 2 * 4 = 4*(b+1)^2 by ring] at heq
        rw [← eq_neg_iff_add_eq_zero] at heq; simp [heq]
      · simp [show 9 + b * 6 + b ^ 2 = (b+3)^2 by ring] at heq
        rw [← eq_neg_iff_add_eq_zero] at heq; simp [heq]
      simp [show 16 + (-(b * 8) - b ^ 2 * 8) = 8*(b+2)*(1-b) by ring] at heq
      rcases heq with h|h
      · rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
      rw [sub_eq_zero] at h; simp [← h]
  -- Similarly in the second case, we have $-4<b$ and $b<2$, so it is easy to find $a$ from the equation.
    replace h1 : (b + 1) ^ 2 < 3 ^ 2 := by omega
    rw [sq_lt_sq] at h1; norm_num at h1
    rw [abs_lt] at h1; rcases h1 with ⟨bgt, blt⟩
    replace agt : -4 < b := by linarith only [bgt]
    replace alt : b < 2 := by linarith only [blt]
    interval_cases b; all_goals rw [← sub_eq_zero] at heq
    all_goals ring_nf at heq
    · simp [show -(a * 24) - a ^ 2 * 8 = -8*a*(a+3) by ring] at heq
      rcases heq with h|h; simp [h]
      rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
    · simp [show (1 - a * 2 + a ^ 2) = (a-1)^ 2 by ring] at heq
      rw [sub_eq_zero] at heq; simp [heq]
    · simp [show 4 + a * 8 + a ^ 2 * 4 = 4*(a+1)^2 by ring] at heq
      rw [← eq_neg_iff_add_eq_zero] at heq; simp [heq]
    · simp [show 9 + a * 6 + a ^ 2 = (a+3)^2 by ring] at heq
      rw [← eq_neg_iff_add_eq_zero] at heq; simp [heq]
    simp [show 16 + (-(a * 8) - a ^ 2 * 8) = 8*(a+2)*(1-a) by ring] at heq
    rcases heq with h|h
    · rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
    rw [sub_eq_zero] at h; simp [← h]
-- Conversely, it is straighforward to check that the listed values for $a$ and $b$ are indeed solutions
  intro h; rcases h with h|h|h|h|h|h|h
  all_goals simp_all