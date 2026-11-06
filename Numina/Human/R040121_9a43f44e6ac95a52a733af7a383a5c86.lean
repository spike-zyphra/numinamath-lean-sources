import Mathlib
open Real

/- Three planets orbit a star circularly in the same plane. Each moves in the same direction and moves at constant speed. Their periods are 60, 84, and 140 years. The three planets and the star are currently collinear. What is the fewest number of years from now that they will all be collinear again?-/



theorem AIME_NumberTheory_732   :
  IsLeast {(t:ℝ) | (t > 0) ∧ (∃ (x: Nat), 2 * π * t / 60-2 * π * t / 84=x*π )∧(∃ (y: Nat), 2 * π * t / 84-2 * π * t / 140=y*π ) }  105 := by


-- Let the planets be A, B, and C, with periods 60, 84, and 140 years, respectively.Let the star be S and the current time be t = 0.
-- Let the angle between the planet A's initial position and it's position after t years be $a(t)$.
-- Let the angle between the planet B's initial position and it's position after t years be $b(t)$.
-- Let the angle between the planet C's initial position and it's position after t years be $c(t)$.

-- We can find $a(t)$, $b(t)$, and $c(t)$ by the following formulas:
-- $a(t) = 2πt/60$
-- $b(t) = 2πt/84$
-- $c(t) = 2πt/140$

-- The planets and the star are collinear if the differences between the angles are all some multiples of pi.
    simp only [IsLeast,lowerBounds]
    simp only [gt_iff_lt, Set.mem_setOf_eq, Nat.ofNat_pos, true_and, and_imp, forall_exists_index]
--We prove that 105 satisfies the conditions.
    rw[←mul_div,←mul_div,←mul_sub,←mul_div,←mul_sub]
    norm_num
    split_ands
    use 1
    field_simp
--We prove that 105 is a lower bound.
    intro t tpos x hx y hy
    rw[←mul_div,←mul_div,←mul_sub,mul_comm,←mul_assoc,mul_left_inj'] at hx hy
    field_simp at hx hy
    ring_nf at hx hy
--Simplify the condition on $t$,$x$ and $y$.
    replace hx:t*6=x*630:=by linarith
    replace hy:t=y*105:=by linarith
--Because $y$ is a natural number, $t$ is a multiple $y$ and $t$ is positive, we know that $1< y$.
    have one_le_y:1≤y:=by
      rw[Nat.one_le_iff_ne_zero]
      apply ne_of_gt
      rw[←@Nat.cast_pos Real]
      linarith
--Because $t=105*y$, we know that $105\le t$
    rw[hy]
    norm_num
    exact one_le_y
    exact pi_ne_zero
    exact pi_ne_zero