import Mathlib

/-
If a b c are positive reals smaller than 1, prove:
a+b+c+2abc>ab+bc+ca+2(abc)^(1/2)
-/
theorem inequalites_92859 (a b c : ℝ) : 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧ c < 1 → a + b + c + 2*a*b*c > a*b + b*c + c*a + 2* √(a*b*c) := by
  intro ⟨_,_,_,_,_,_⟩
  -- two auxillary inequality
  have pab : 0 < a*b := by
    apply mul_pos
    repeat assumption
  have pabc : 0 < a*b*c := by
    repeat apply mul_pos
    repeat assumption
  
  -- transform the goal using algebraic identities
  suffices 1 - 2*√(a*b*c) + a*b*c > 1 - a - b - c + a*b+ a*c + b*c - a*b*c by linarith
  suffices (1 - a) * (1 - b) * (1 - c) < (1 - √(a*b*c))^2 by
    have : 1 - a - b - c + a*b+ a*c + b*c - a*b*c = (1 - a)* (1 - b) * (1 - c) := by ring
    rw [this]
    have : 1 - 2*√(a*b*c) + a*b*c = (1 - √(a*b*c))^2 := by
      nth_rewrite 2 [← Real.sq_sqrt pabc.le]
      ring
    rw [this]
    assumption
  
  -- split the inequality into 3 steps
  -- first: (1 - a) * (1 - b) * (1 - c) < (1 - a) * (1- b)
  apply lt_of_lt_of_le
  show (1 - a) * (1 - b) * (1 - c) < (1 - a) * (1- b)
  rw [mul_lt_iff_lt_one_right]
  linarith
  apply mul_pos
  repeat linarith

  -- next: (1 - a) * (1- b) ≤ (1 - √(a * b)) ^ 2
  -- this is nothing but Cauchy-Schwarz
  apply le_trans
  show (1 - a) * (1- b) ≤ (1 - √(a * b)) ^ 2
  · let x := √a
    let y := √b
    have : √(a*b) = x * y := by rw [Real.sqrt_mul]; linarith
    rw [this]
    have : a = x^2 := by rw [Real.sq_sqrt]; linarith
    rw [this]
    have : b = y^2 := by rw [Real.sq_sqrt]; linarith
    rw [this]
    have : (1 - x ^ 2) * (1 - y ^ 2) = 1 - x^2 -y^2 + x^2 * y^2 := by ring
    rw [this]
    have : (1 - x * y) ^ 2 = 1 - 2 * x * y + x^2 * y^2 := by ring
    rw [this]
    suffices 0 ≤ x^2 - 2*x*y + y^2 by linarith
    convert sq_nonneg (x - y)
    ring
  
  --finally: (1 - √(a * b)) ^ 2 ≤ (1 - √(a * b * c)) ^ 2
  apply sq_le_sq'
  apply le_trans
  show -(1 - √(a * b * c)) ≤ 0
  simp
  apply le_of_lt
  suffices a * b * c < 1 * 1 * 1 by simp at this; exact this
  repeat apply mul_lt_mul
  repeat linarith
  simp
  apply le_of_lt
  suffices a * b < 1 * 1 by simp at this; exact this
  apply mul_lt_mul
  repeat linarith
  suffices √(a * b * c) ≤ √(a * b) by linarith
  rw [Real.sqrt_mul]
  rw [mul_le_iff_le_one_right]
  rw [Real.sqrt_le_iff]
  simp
  linarith
  rw [Real.sqrt_pos]
  repeat linarith