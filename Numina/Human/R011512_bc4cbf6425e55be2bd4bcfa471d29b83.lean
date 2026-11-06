import Mathlib

/-
Find the primes $p$ such that there exist $x, y \in \mathbb{N}^{*}$ such that

$$
x\left(y^{2}-p\right)+y\left(x^{2}-p\right)=5 p
$$
-/
theorem number_theory_253487:
IsLeast {x:ℝ | ∃ a:ℕ, ∃b : ℕ, ∃ c:ℕ, a≠b ∧ a≠c ∧ b≠c ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ x = ((a * b * c): ℝ) / (a + b + c)} 1 := by
  unfold IsLeast lowerBounds
  simp
  
  -- verify 1 is in the set by letting a = 1 b = 2 and c = 3.
  constructor
  use 1, 2
  simp
  use 3
  simp
  norm_num

  intro r
  intro a b hab c hac hbc apos bpos cpos h

  --Wlog a < b < c.
  wlog alb : a < b
  have bla : b < a := by omega
  apply this
  have : ¬ b = a := by omega
  exact this
  exact hbc
  exact hac
  exact bpos
  exact apos
  exact cpos
  nth_rw 2 [mul_comm]
  nth_rw 2 [add_comm]
  exact h
  exact bla

  wlog blc : b < c
  have clb : c < b := by omega
  by_cases alc : a < c
  apply this
  exact hac
  exact hab
  omega
  exact apos
  exact cpos
  exact bpos
  rw [mul_assoc,add_assoc]
  nth_rw 2 [mul_comm,add_comm]
  rw [←mul_assoc, ←add_assoc]
  exact h
  exact alc
  exact clb
  have cla : c < a := by omega
  apply this
  have : ¬ c = a := by omega
  exact this
  have : ¬ c = b := by omega
  exact this
  exact hab
  exact cpos
  exact apos
  exact bpos
  have : (c:ℝ) * a * b = a*b*c := by ring
  rw [this]
  have : (c:ℝ)+a+b = a+b+c := by ring
  rw [this]
  exact h
  exact cla
  exact alb

  --If b≥3, then abc ≥ 3c while a+b+c ≤ 3c, we geet abc/(a+b+c) ≥ 1.
  by_cases bge2 : 3 ≤ b
  have nu: 3*c ≤ (a:ℝ)*b*c := by 
    have t1: 3*c ≤ b*c := by nlinarith
    have t2: b*c ≤ a*b*c := by nlinarith
    rify at t1 t2
    linarith
  have de: (a:ℝ)+b+c ≤ 3*c := by norm_cast; linarith
  rw [h]
  rw [@one_le_div_iff]
  constructor
  constructor
  norm_cast; linarith
  linarith

  by_cases ble1 : b ≤ 1
  omega

  --Otherwise, we must have b = 2 and a = 1.
  have be : b = 2 := by omega
  have ae : a = 1 := by omega
  have cge3 : 3 ≤ c := by omega
  rw [ae,be] at h
  field_simp at h
  norm_cast at h
  ring_nf at h
  --Then, no matter what c is, we have abc/(a+b+c) ≥ 1.
  have : (3+c) ≤ @Nat.cast ℝ AddMonoidWithOne.toNatCast (c * 2) := by 
    norm_cast
    linarith
  by_contra rl1
  push_neg at rl1
  have : r * ↑(3 + c) < ((3+c):ℝ) := by field_simp; exact rl1
  linarith