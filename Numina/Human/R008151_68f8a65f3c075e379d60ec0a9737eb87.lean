import Mathlib

/- Find $120_4\times13_4\div2_4$. Express your answer in base 4. -/
theorem number_theory_12345{a b : ℕ}
  (ha: Nat.digits 4 a = [0, 2, 1])
  (hb: Nat.digits 4 b = [3, 1])
  (hc: Nat.digits 4 c = [2]):
  Nat.digits 4 (a * b / c) = [0, 1, 1, 1] := by
  -- 120 (base 4) is 1x4^2+2x4=16+8=24
  have h1: a = 24 := by
    rw [← Nat.ofDigits_digits 4 a]
    rw [ha]
    repeat rw [Nat.ofDigits]
    simp
  -- and 13 (base 4) is 1x4+3=7.
  have h2: b = 7 := by
    rw [← Nat.ofDigits_digits 4 b]
    rw [hb]
    repeat rw [Nat.ofDigits]
    simp
  -- 2 (base 4) is just 2.
  have h3: c = 2 := by
    rw [← Nat.ofDigits_digits 4 c]
    simp [hc]
  -- so 120_4 x 13_4 / 2_4 = 24x7/2 = 12x7 = 4x(3x7)
  -- = 4x(1+5x4)=4x(1+4x(1+4x1)). so answer is 1110 (base 4)
  have h4: a * b / c = 4 * (1 + 4 * (1 + 4 * 1)) := by
    rw [h1,h2,h3]
  have h5: Nat.ofDigits 4 [0,1,1,1] = 4 * (1 + 4 * (1 + 4 * 1)) := by
    repeat rw [Nat.ofDigits]
    simp
  rw [h4, ← h5]
  rw [Nat.digits_ofDigits]
  norm_num; simp; simp