import Mathlib

open Real

/- What is the smallest positive integer n such that $\sqrt{n}-\sqrt{n-1}<0.01$
(A) 2499 (B) 2500 (C) 2501 (D) 10,000 (E) There is no such integer -/
theorem inequalities_92996 : IsLeast {n : ℕ | 0 < n ∧ √n - √(n - 1) < 0.01} 2501 := by
  -- 2501 is the smallest positive integer n such that sqrt(n) - sqrt(n-1) < 0.01
  have sq50: √2500=50 := by
    rw[sqrt_eq_iff_mul_self_eq]
    norm_num;norm_num;norm_num
  -- 50^2 = 2500
  simp only [IsLeast,lowerBounds,Set.mem_setOf_eq, Nat.ofNat_pos, Nat.cast_ofNat, true_and, and_imp]
  rw [sub_lt_iff_lt_add]
  constructor
  -- We will show that 2501 is a positive integer $n$ such that $\sqrt(n) - \sqrt(n-1) < 0.01$.
  rw [sqrt_lt]
  -- Taking square on both sides, it suffices to show that $1<1/10000+50/50$
  norm_num
  ring_nf
  norm_num
  rw [sq50]
  all_goals try linarith
  -- We will show that any positive integer $n$ such that $\sqrt(n) - \sqrt(n-1) < 0.01$ is at least 2501.
  intro a apos ha
  -- It suffices to show that $2500< n$ as natural numbers are discrete.
  apply Nat.le_of_pred_lt
  norm_num
  rw [←@Nat.cast_lt Real]
  rw[sub_lt_iff_lt_add] at ha
  -- Taking square on both sides.
  rw [sqrt_lt] at ha
  ring_nf at ha
  rw [sq_sqrt] at ha
  rw [←sub_lt_iff_lt_add,add_comm (1/10000),←sub_lt_iff_lt_add] at ha
  field_simp at ha
  rw [lt_div_iff₀] at ha
  rw [lt_sqrt] at ha
  --Taking square on both sides, we know that $n-1>50*(9999/10000)>2499$.
  norm_num at ha
  apply lt_trans' ha
  norm_num
  all_goals try norm_num
  apply Nat.one_le_of_lt apos
  apply add_nonneg (by norm_num) (by norm_num)