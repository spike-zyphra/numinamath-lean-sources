import Mathlib

theorem number_theory_4735_1 (x y z : ℕ) : x+y≡1[MOD 7] ∧ x+z≡2[MOD 7] ∧ y+z≡3[MOD 7] ↔
    x ≡ 0 [MOD 7] ∧ y ≡ 1 [MOD 7] ∧ z ≡ 2 [MOD 7] := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  constructor
  . rintro ⟨h1, h2, h3⟩
--      We can express \(y\) in terms of \(x\):
-- \[ y \equiv 1 - x \mod 7. \]
    have hy : (y : ZMod 7) = 1 - (x : ZMod 7) := by linear_combination h1
--      Next, we substitute \(y\) into the second equation \(x + z \equiv 2 \mod 7\):
-- \[ x + z \equiv 2 \mod 7 \Rightarrow z \equiv 2 - x \mod 7. \]
    have hz : (z : ZMod 7) = 2 - (x : ZMod 7) := by linear_combination h2
--      Now, we substitute both \(y\) and \(z\) into the third equation \(y + z \equiv 3 \mod 7\):
-- \[ (1 - x) + (2 - x) \equiv 3 \mod 7 \Rightarrow 3 - 2x \equiv 3 \mod 7. \]
-- This simplifies to:
-- \[ -2x \equiv 0 \mod 7 \Rightarrow x \equiv 0 \mod 7. \]
    rw [hy, hz] at h3
    ring_nf at h3
    have hx : 2 * (x : ZMod 7) = 0 := by linear_combination -h3
    rw [mul_eq_zero] at hx
    refine hx.elim (fun hx => ?_) (fun hx => ?_)
    . rw [show (2 : ZMod 7) = Nat.cast 2 from rfl, show (0 : ZMod 7) = Nat.cast 0 from rfl] at hx
      apply_fun ZMod.val at hx
      rw [ZMod.val_natCast, ZMod.val_natCast] at hx
      norm_num at hx
    . -- Substituting \(x \equiv 0\) back, we find:
-- \[ y \equiv 1 \mod 7, \quad z \equiv 2 \mod 7. \]
      rw [hx, sub_zero] at hy
      rw [hx, sub_zero] at hz
      split_ands <;> assumption
  . rintro ⟨hx, hy, hz⟩
    rw [hx, hy, hz]
    simp [show 1+2=(3 : ZMod 7) from rfl]

theorem number_theory_4735_2 (x y z : ℕ) : x+2*y+3*z≡1[MOD 7] ∧ x+3*y+5*z≡1[MOD 7] ∧ x+4*y+6*z≡1[MOD 7] ↔
    x ≡ 1 [MOD 7] ∧ y ≡ 0 [MOD 7] ∧ z ≡ 0 [MOD 7] := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simp only [← ZMod.eq_iff_modEq_nat]
  push_cast
  constructor
  . rintro ⟨h1, h2, h3⟩
--      We can subtract the first equation from the second:
-- \[ (x + 3y + 5z) - (x + 2y + 3z) \equiv 0 \mod 7 \Rightarrow y + 2z \equiv 0 \mod 7 \Rightarrow y \equiv -2z \mod 7. \]
    have hy1 : (y : ZMod 7) = -2* (z : ZMod 7) := by linear_combination h2 - h1
--      Next, we subtract the second equation from the third:
-- \[ (x + 4y + 6z) - (x + 3y + 5z) \equiv 0 \mod 7 \Rightarrow y + z \equiv 0 \mod 7 \Rightarrow y \equiv -z \mod 7. \]
    have hy2 : (y : ZMod 7) = -1* (z : ZMod 7) := by linear_combination h3 - h2
--      Setting these equal gives:
-- \[ -2z \equiv -z \mod 7 \Rightarrow -z \equiv 0 \mod 7 \Rightarrow z \equiv 0 \mod 7. \]
    have hz : (z : ZMod 7) = 0 := by linear_combination hy1 - hy2
--      Substituting \(z \equiv 0\) back, we find:
-- \[ y \equiv 0 \mod 7. \]
    rw [hz, mul_zero] at hy1
--      Substituting \(y\) and \(z\) into the first equation gives:
-- \[ x + 2(0) + 3(0) \equiv 1 \mod 7 \Rightarrow x \equiv 1 \mod 7. \]
    rw [hy1, hz, mul_zero, mul_zero, add_zero, add_zero] at h1
    exact ⟨h1, hy1, hz⟩
  rintro ⟨hx, hy, hz⟩
  rw [hx, hy, hz]
  simp

theorem number_theory_4735_3 (x y z w : ℕ) : x+y+z≡1[MOD 7] ∧ x+y+w≡1[MOD 7] ∧
    x+z+w≡1[MOD 7] ∧ y+z+w≡1[MOD 7] ↔
    x ≡ 5 [MOD 7] ∧ y ≡ 5 [MOD 7] ∧ w ≡ 5 [MOD 7] ∧ z ≡ 5 [MOD 7]:= by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [Nat.ModEq] at h₁ h₂ h₃ h₄ ⊢
    omega
  rintro ⟨h₁, h₂, h₃, h₄⟩
  simp [Nat.ModEq] at h₁ h₂ h₃ h₄ ⊢
  omega