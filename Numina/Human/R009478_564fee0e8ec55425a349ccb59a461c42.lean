import Mathlib

/-Given that $x>0$, determine whether it is a necessary condition, a sufficient condition, a necessary and sufficient condition, or neither for the inequality $(x-2)(x-4)<0$.-/
theorem algebra_9143 :
    (∀ x : ℝ, (x - 2) * (x - 4) < 0 → x > 0) ∧ ¬ (∀ x : ℝ, x > 0 → (x - 2) * (x - 4) < 0) := by
  -- divide the problem into two parts
  constructor
  intro x hyp
  -- to prove $(x - 2)(x - 4) < 0$ implies $x<0$, suppose not.
  by_contra p; simp only [gt_iff_lt, not_lt] at p
  -- then consider $x-2<0$, $x-4<0$ when $x<0$, which implies $(x-2)(x-4)>0$, which contridicts the condition.
  have neg₁: x - 2 < 0 := by linarith
  have neg₂: x - 4 < 0 := by linarith
  have : (x - 2) * (x - 4) > 0 := mul_pos_of_neg_of_neg neg₁ neg₂
  linarith
  -- with regard to the other side, we only need to give a counterexample. $x=2$ will do.
  simp only [gt_iff_lt, not_forall, Classical.not_imp, not_lt]
  use 2; simp only [sub_self, zero_mul, le_refl, Nat.ofNat_pos, exists_const]