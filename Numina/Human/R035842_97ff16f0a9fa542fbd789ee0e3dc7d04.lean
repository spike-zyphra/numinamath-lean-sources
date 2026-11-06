import Mathlib
open Real

/- If the real numbers $a$, $b$ satisfy ${{(2a+b)}^{2}}+\frac{|2{{a}^{2}}-32|}{\sqrt{3-a}}=0$, $a=$ ___, $b=$___. -/
theorem algebra_1652 {a b : ℝ} (h : (2 * a + b) ^ 2 + abs (2 * a ^ 2 - 32) / sqrt (3 - a) = 0) (ha1 : sqrt (3 - a) ≠ 0) (ha2 : 3 - a > 0) : a = -4 ∧ b = 8 := by -- Lean4 does not default to expressions where the denominator is not equal to 0 and the equation within the root is greater than or equal to 0. Lean4 assumes that 1/0=0, Real.sqrt (-1)=-1, etc. Therefore, it is necessary to add conditions where the denominator is not equal to 0 and the equation within the root is greater than or equal to 0
  have h1 : (2*a+b)^2≥0 := by nlinarith
  have h2 : abs (2 * a ^ 2 - 32) ≥ 0 := by apply abs_nonneg
  have h3 : sqrt (3-a)≥0 := by apply sqrt_nonneg
  have h4 := div_nonneg h2 h3
  have h5 := add_nonneg h1 h4
  have h1' : (2*a+b)^2≤0 := by linarith
  have h4' : |2 * a ^ 2 - 32| / √(3 - a) ≤ 0 := by linarith
  have hh1 := le_antisymm h1 h1'
  have hh2 := le_antisymm h4 h4'
  have hh1 : 2 * a + b = 0 := by nlinarith
  have hh2 : 2 * a ^ 2 - 32 = 0 := by
    have := div_eq_zero_iff.1 hh2.symm
    match this with
    | Or.inl hh =>
      simp at hh
      exact hh
    | Or.inr hh' =>
      have := ha1 hh' -- False
      contradiction
  have hh2 : a^2=4^2 := by linarith
  have ha : a=-4 := by
    match eq_or_eq_neg_of_sq_eq_sq a 4 hh2 with
    | Or.inl hh =>
      rw [hh] at ha2
      rw [show 3-4>(0:ℝ) ↔ False by norm_num] at ha2
      contradiction
    | Or.inr hh =>
      exact hh
  rw [ha] at hh1
  have hb : b = 8 := by linarith
  exact ⟨ha,hb⟩
