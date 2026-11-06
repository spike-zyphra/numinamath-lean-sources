import Mathlib
set_option maxHeartbeats 800000
/- 8. If $a$, $b$, $c$ are distinct integers, then
$$
3 a^{2}+2 b^{2}+4 c^{2}-a b-3 b c-5 c a
$$

the minimum value is $\qquad$ -/
theorem algebra_202712 : IsLeast {S : ℤ | ∃ a b c : ℤ, (a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ S = 3 * a ^ 2 + 2 * b ^ 2 + 4 * c ^ 2 - a * b - 3 * b * c - 5 * c * a)} 6 := by
  constructor
  -- First part: Prove that 6 is in the set by providing a specific example
  .
    use 1, -1, 0
    norm_num
  -- Second part: Prove that 6 is a lower bound for all elements in the set
  .
    simp [lowerBounds]
    intro S a b ha c hb hc hS
    subst S
    -- Since a ≠ b, we know (a - b)² > 0
    have h1:= sq_pos_of_ne_zero (show a - b ≠ 0 by exact sub_ne_zero_of_ne ha)
    -- Since b ≠ c, we know (b - c)² > 0
    have h2:= sq_pos_of_ne_zero (show b - c ≠ 0 by exact sub_ne_zero_of_ne hb)
    -- Since a ≠ c, we know (a - c)² > 0
    have h3:= sq_pos_of_ne_zero (show a - c ≠ 0 by exact sub_ne_zero_of_ne hc)
    -- For integers, if x ≠ 0, then x² ≥ 1
    replace h1 : (a - b) ^ 2 ≥ 1:= by omega
    replace h2 : (b - c) ^ 2 ≥ 1:= by omega
    replace h3 : (a - c) ^ 2 ≥ 1:= by omega
    -- The key inequality to prove the minimum value
    suffices (a - b) ^ 2 + 3 * (b - c) ^ 2 + 5 * (a - c) ^ 2 > 10 by linarith
    nlinarith
