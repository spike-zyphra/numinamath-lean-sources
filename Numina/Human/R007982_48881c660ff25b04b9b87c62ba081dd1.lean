import Mathlib
/- Let a, b and c be three distinct one-digit numbers.
What is the maximum value of the sum of the roots of the equation (x-a)(x-b)+(x-b)(x-c)=0?
(A) 15
(B) 15.5
(C) 16
(D) 16.5
(E) 17
-/
theorem algebra_96708
: IsGreatest {t | ∃ a b c:ℕ, ∃ x y:ℝ, a≠b ∧ b≠c ∧ c≠a ∧ a ∈ Set.Icc 0 9 ∧
b ∈ Set.Icc 0 9 ∧ c ∈ Set.Icc 0 9 ∧ x ≠ y ∧ (x-a)*(x-b)+(x-b)*(x-c)=0 ∧ (y-a)*(y-b)+(y-b)*(y-c)=0 ∧
t = x+y} 16.5 := by
  -- we first simplify the notation
  unfold IsGreatest; simp
  constructor
  -- let's first show 16.5 is the upper bound
  rotate_left
  unfold upperBounds
  intro t
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro a b hab c hbc hca ha hb hc x y hxy hx hy h4
  rw [h4]; clear h4
  -- we can factor the equation
  conv_lhs at hx =>
    calc (x-a) * (x-b) + (x-b) * (x-c)
    _ = (x-b) * (2*x-a-c) := by ring_nf
  conv_lhs at hy =>
    calc (y-a) * (y-b) + (y-b) * (y-c)
    _ = (y-b) * (2*y-a-c) := by ring_nf
  simp at hx hy
  -- now we do case analysis on the values of a, b, c
  -- fortunately the case where b<9 is easy to eliminate
  cases' hx with hx1 hx2
  · cases' hy with hy1 hy2
    · exfalso; apply hxy; linarith
    · have :x=b:= by linarith
      rw [this]
      have :y=(a+c)/2:= by linarith
      rw [this]
      -- the conclusion is obvious but annoying to prove
      have :b=9∨b<=8 := by omega
      cases' this with hb9 hblt9
      · rw [hb9]
        have ha': a+c ≤ 15 := by omega
        norm_cast
        conv_rhs =>
          calc (16.5:ℝ)
          _ = 9+7.5 := by norm_num
        apply add_le_add
        norm_num
        norm_num
        exact div_le_div₀ (c:=(15:ℝ)) (by norm_num) (by norm_cast) (by norm_num) (by norm_num)
      · conv_rhs =>
          calc (16.5:ℝ)
          _ = 8+8.5 := by norm_num
        apply add_le_add
        norm_cast
        norm_num
        exact div_le_div₀ (c:=(17:ℝ)) (by norm_num) (by norm_cast; omega) (by norm_num) (by rfl)
  · cases' hy with hy1 hy2
    · have :x=(a+c)/2:= by linarith
      rw [this]
      have :y=b:= by linarith
      rw [this]
      -- the conclusion is obvious but annoying to prove (so we copy paste)
      rw [add_comm]
      have :b=9∨b<=8 := by omega
      cases' this with hb9 hblt9
      · rw [hb9]
        have ha': a+c ≤ 15 := by omega
        norm_cast
        conv_rhs =>
          calc (16.5:ℝ)
          _ = 9+7.5 := by norm_num
        apply add_le_add
        norm_num
        norm_num
        exact div_le_div₀ (c:=(15:ℝ)) (by norm_num) (by norm_cast) (by norm_num) (by norm_num)
      · conv_rhs =>
          calc (16.5:ℝ)
          _ = 8+8.5 := by norm_num
        apply add_le_add
        norm_cast
        norm_num
        exact div_le_div₀ (c:=(17:ℝ)) (by norm_num) (by norm_cast; omega) (by norm_num) (by rfl)
    · exfalso; apply hxy; linarith;
  -- now we have to prove the upper bound is reachable
  -- from previous result it's clear that a=7, b=9, c=8 (or flipped version with (8, 9, 7))
  -- will reach 16.5
  -- The actual proof is just dealing with the assumption
  use 7, 9
  constructor
  · norm_num
  use 8
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  use 9, (7.5:ℝ)
  constructor
  · norm_num
  · norm_num