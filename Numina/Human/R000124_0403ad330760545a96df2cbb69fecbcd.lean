import Mathlib

/- a)
$$\begin{array}{r}
2 x + 3 y \equiv 5 \pmod{7} \\
x + 5 y \equiv 6 \pmod{7}
\end{array}$$-/
theorem number_theory_4728_1 (x y : ℕ) : (2*x+3*y≡5[MOD 7] ∧ x+5*y≡6[MOD 7]) ↔
    (x≡2*y+6[MOD 7]) := by
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  constructor
  . rintro ⟨_, h2⟩
--      First, we can express \( x \) from the second equation:
-- $$ x \equiv 6 - 5y \pmod{7} $$
    have hx : (x : ZMod 7) = 6 - 5 * (y : ZMod 7) := by linear_combination h2
--      Now, substitute this expression for \( x \) into the first equation:
-- $$ 2(6 - 5y) + 3y \equiv 5 \pmod{7} $$
-- This simplifies to:
-- $$ 12 - 10y + 3y \equiv 5 \pmod{7} $$
-- Combining like terms gives:
-- $$ 12 - 7y \equiv 5 \pmod{7} $$
-- Reducing \( 12 \) modulo \( 7 \) gives \( 5 \):
-- $$ 5 - 7y \equiv 5 \pmod{7} $$
-- This simplifies to:
-- $$ -7y \equiv 0 \pmod{7} $$
-- Since \( -7 \equiv 0 \pmod{7} \), this is always true, meaning \( y \) can take any value.
    rwa [sub_eq_add_neg, neg_mul_eq_neg_mul, show -5 = (2 : ZMod 7) from rfl, add_comm] at hx
  intro hx
  constructor
  . rw [hx]
    ring_nf
    rw [show (7 : ZMod 7) = 0 from rfl, mul_zero, add_zero]
    rfl
  . rw [hx]
    ring_nf
    rw [show (7 : ZMod 7) = 0 from rfl, mul_zero, add_zero]

/- b)
$$\begin{aligned}
4 x + y & \equiv 5 \pmod{7} \\
x + 2 y & \equiv 4 \pmod{7}
\end{aligned}$$-/
theorem number_theory_4728_2 (x y : ℕ) : (4*x+y≡5[MOD 7] ∧ x+2*y≡4[MOD 7]) ↔
    False := by
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  rw [iff_false, not_and]
  intro h1 h2
--    We can express \( y \):
-- $$ y \equiv 5 - 4x \pmod{7} $$
  have hy : (y : ZMod 7) = 5 - 4 * (x : ZMod 7) := by linear_combination h1
--    Substituting this into the second equation:
-- $$ x + 2(5 - 4x) \equiv 4 \pmod{7} $$
  rw [hy] at h2
--    This simplifies to:
-- $$ x + 10 - 8x \equiv 4 \pmod{7} $$
-- Combining like terms gives:
-- $$ -7x + 10 \equiv 4 \pmod{7} $$
-- Reducing \( 10 \) modulo \( 7 \) gives \( 3 \):
-- $$ -7x + 3 \equiv 4 \pmod{7} $$
-- This simplifies to:
-- $$ -7x \equiv 1 \pmod{7} $$
  ring_nf at h2
--    Since \( -7 \equiv 0 \pmod{7} \), this implies:
-- $$ 0 \equiv 1 \pmod{7} $$
-- This is a contradiction, indicating that there are no solutions to this system.
  rw [show (7 : ZMod 7) = 0 from rfl, mul_zero, sub_zero] at h2
  norm_cast at h2
