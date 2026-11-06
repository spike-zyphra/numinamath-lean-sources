import Mathlib

/- a)
$$\begin{array}{r}
x + 2y \equiv 1 \pmod{5} \\
2x + y \equiv 1 \pmod{5}
\end{array}$$-/
theorem number_theory_4727_1 (x y : ℕ) : (x+2*y≡1[MOD 5] ∧ 2*x+y≡1[MOD 5]) ↔
    (x≡2[MOD 5] ∧ y≡2[MOD 5]) := by
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  constructor
  . rintro ⟨h1, h2⟩
  --    Rearranging gives us:
  --  $$x \equiv 1 - 2y \pmod{5}$$
    have hx : (x : ZMod 5) = 1 - 2 * (y : ZMod 5) := by linear_combination h1
    rw [hx] at h2
  --    Which simplifies to:
  --  $$3y \equiv 1 \pmod{5}$$
    have hy : 3 * (y : ZMod 5) = 1 := by linear_combination -h2
  --    The multiplicative inverse of 3 modulo 5 is 2, so we multiply both sides by 2:
  --  $$y \equiv 2 \pmod{5}$$
    apply_fun (2 * ·) at hy
    rw [← mul_assoc, show (2 : ZMod 5) * 3 = 1 from rfl, one_mul, mul_one] at hy
  --    Substituting \(y = 2\) back into the expression for \(x\):
  --  $$x \equiv 1 - 2(2) \equiv 1 - 4 \equiv -3 \equiv 2 \pmod{5}$$
    rw [hy, show (1 : ZMod 5) - 2 * 2 = 2 from rfl] at hx
    exact ⟨hx, hy⟩
  . rintro ⟨hx, hy⟩
    simp [hx, hy]
    exact ⟨rfl, rfl⟩

/- b)
$$\begin{aligned}
x + 3y & \equiv 1 \pmod{5} \\
3x + 4y & \equiv 2 \pmod{5}
\end{aligned}$$-/
theorem number_theory_4727_2 (x y : ℕ) : (x+3*y≡1[MOD 5] ∧ 3*x+4*y≡2[MOD 5]) ↔
    False := by
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  rw [iff_false, not_and]
  intro h1 h2
  --  From the first equation, we can express \(x\):
  --  $$x \equiv 1 - 3y \pmod{5}$$
  have hx : (x : ZMod 5) = 1 - 3 * (y : ZMod 5) := by linear_combination h1
  --  Substituting this into the second equation:
  --  $$3(1 - 3y) + 4y \equiv 2 \pmod{5}$$
  rw [hx] at h2
  --  Simplifying gives:
  --  $$3 - 9y + 4y \equiv 2 \pmod{5}$$
  --  $$3 - 5y \equiv 2 \pmod{5}$$
  ring_nf at h2
  --   This simplifies to:
  --  $$3 \equiv 2 \pmod{5}$$
  --  This is a contradiction, indicating that there is no solution for this system.
  rw [show (5 : ZMod 5) = 0 from rfl, mul_zero, sub_zero] at h2
  norm_cast at h2

/- c)
$$\begin{array}{l}
4x + y \equiv 2 \pmod{5} \\
2x + 3y \equiv 1 \pmod{5}
\end{array}$$-/
theorem number_theory_4727_3 (x y : ℕ) : (4*x+y≡2[MOD 5] ∧ 2*x+3*y≡1[MOD 5]) ↔
    y≡x+2[MOD 5] := by
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  constructor
  . rintro ⟨h1, _⟩
  --    From the first equation, we can express \(y\):
  --  $$y \equiv 2 - 4x \pmod{5}$$
    have hy : (y : ZMod 5) = 2 - 4 * (x : ZMod 5) := by linear_combination h1
  --     Substituting this into the second equation:
  --  $$2x + 3(2 - 4x) \equiv 1 \pmod{5}$$
  --  Simplifying gives:
  --  $$2x + 6 - 12x \equiv 1 \pmod{5}$$
  --  $$-10x + 6 \equiv 1 \pmod{5}$$
  --  Reducing modulo 5:
  --  $$0 - 10x + 1 \equiv 1 \pmod{5}$$
  --  This simplifies to:
  --  $$-10x \equiv 0 \pmod{5}$$
    rwa [sub_eq_add_neg, neg_mul_eq_neg_mul, show -(4 : ZMod 5) = 1 from rfl, one_mul, add_comm] at hy
  intro hy
  constructor
  . rw [hy]
    ring_nf
    rw [show (5 : ZMod 5) = 0 from rfl, mul_zero, add_zero]
  . rw [hy]
    ring_nf
    rw [show (5 : ZMod 5) = 0 from rfl, mul_zero, add_zero, show (6 : ZMod 5) = 1 from rfl]
