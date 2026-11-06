import Mathlib
set_option maxRecDepth 2000

open Real

/-27. Given positive integers $a, b$ satisfy $\sqrt{2020 a}+\sqrt{2020 b}-\sqrt{2020 a b}=a \sqrt{b}+b \sqrt{a}-2020$, then the minimum value of $\sqrt{a+b}$ is $\qquad$-/
theorem algebra_240876 : IsLeast {t : ℝ | ∃ a b : ℕ, t = √(↑a + ↑b) ∧ 0 < a ∧ 0 < b
    ∧ √(2020 * a) + √(2020 * b) - √(2020 * a * b) = a * √b + b * √a - 2020} 11 := by
  simp [IsLeast, lowerBounds]; constructor
  -- Prove that $11$ can be achieved by $a=20$, $b=101$
  · use 20, 101; norm_num
    nth_rw 4 [show 2020 = (√20 * √101)^2 by norm_num [mul_pow]]
    nth_rw 3 [show 20 = √20^2 by norm_num]
    nth_rw 4 [show 101 = √101^2 by norm_num]
    rw [show √2020 = √101 * √20 by norm_num [← sqrt_mul]]
    ring_nf; simp; symm
    norm_num [sqrt_eq_iff_eq_sq]
-- Prove that $11$ is an lower bound of the set inquestion
  intro t a b ht apos bpos hab
  rw [sub_eq_sub_iff_add_eq_add] at hab
  have : √2020 * √a + √2020 * √b + 2020 = √2020 * (√a + √b + √2020) := by
    nth_rw 3 [show 2020 = √2020^2 by norm_num]
    ring
  rw [this] at hab; replace this : a * √b + b * √a + √2020 * √a * √b =
  √a * √b * (√a + √b + √2020) := by
    nth_rw 1 [show a = √a^2 by simp]
    nth_rw 2 [show b = √b^2 by simp]
    ring
  rw [this, mul_right_cancel_iff_of_pos, ← sqrt_mul] at hab
  clear this; rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at hab
  simp [mul_pow] at hab; norm_cast at hab
-- Simplify the assumption and the goal, assume w. l. o. g. $a ≤ b$
  rw [ht]; clear ht t; wlog aleb : a ≤ b
  · specialize this b a; rw [add_comm]
    apply this; any_goals assumption
    rw [hab, mul_comm]; omega
  rw [le_sqrt]; norm_cast
-- Prove that $a$ is a divisor of $2020$ and discuss all possible values of $a$, the goal will follow
  have : a ∈ Nat.divisors 2020 := by
    simp; use b
  rw [show Nat.divisors 2020 = {1, 2, 4, 5, 10, 20, 101, 202, 404, 505, 1010, 2020} by norm_cast] at this
  simp at this; rcases this with ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha
  any_goals rw [ha] at hab
  any_goals omega
  all_goals positivity