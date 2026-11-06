import Mathlib

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

theorem number_theory_4727_3 (x y : ℕ) : (4*x+y≡2[MOD 5] ∧ 2*x+3*y≡1[MOD 5]) ↔
    y≡x+2[MOD 5] := by
  constructor
  · -- Assume (4*x+y≡2[MOD 5] ∧ 2*x+3*y≡1[MOD 5]), prove y≡x+2[MOD 5]
    rintro ⟨h₁, h₂⟩
    simp [Nat.ModEq] at *
    omega
  · -- Assume y≡x+2[MOD 5], prove (4*x+y≡2[MOD 5] ∧ 2*x+3*y≡1[MOD 5])
    intro h
    simp [Nat.ModEq] at h ⊢
    constructor
    · -- Show 4*x + y ≡ 2 [MOD 5]
      omega
    · -- Show 2*x + 3*y ≡ 1 [MOD 5]
      omega