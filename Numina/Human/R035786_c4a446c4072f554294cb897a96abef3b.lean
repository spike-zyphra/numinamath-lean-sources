import Mathlib

/-
11. Let $a, b, c$ be distinct positive integers. Then the minimum value of $\frac{a b c}{a+b+c}$ is . $\qquad$
-/

theorem number_theory_309838 : IsLeast {x : ℤ | ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = (a:ℝ) * b * c / (a + b + c)} 1 := by 
  unfold IsLeast
  simp
  constructor
  use 1; simp
  use 2; simp
  use 3; simp
  field_simp; ring

  unfold lowerBounds
  simp

  intro r a apos b bpos c cpos aneb anec bnec h

  wlog clb : c < b
  have blc: b < c := by omega
  apply this
  exact apos
  exact cpos
  exact bpos
  exact anec
  exact aneb
  linarith
  rw [h]; ring
  exact blc

  wlog bla : b < a
  have alb : a < b := by omega
  by_cases alc : a < c
  apply this
  exact bpos
  exact cpos
  exact apos
  exact bnec
  linarith
  linarith
  rw [h]; ring
  exact alc
  exact clb

  have cla : c < a := by omega
  apply this
  exact bpos
  exact apos
  exact cpos
  linarith
  exact bnec
  exact anec
  rw [h]; ring
  exact cla
  exact alb


  have : 1 ≤ c := by omega
  have : 2 ≤ b := by omega
  have : 3 ≤ a := by omega
  have : 1 ≤ (c:ℝ) := by norm_cast
  have : 2 ≤ (b:ℝ) := by norm_cast
  have : 3 ≤ (a:ℝ) := by norm_cast
  have : 0 < (a:ℝ) * (b:ℝ) * (c:ℝ) := by positivity
  have t1: 2 ≤ b*c := by nlinarith
  have t2: 3 ≤ c*a := by nlinarith
  have t3: 6 ≤ a*b := by nlinarith
  have : (1:ℝ) / (b*c) ≤ 1/2 := by rify at t1; refine one_div_le_one_div_of_le ?_ t1; linarith
  have : (1:ℝ) / (c*a) ≤ 1/3 := by rify at t2; refine one_div_le_one_div_of_le ?_ t2; linarith
  have : (1:ℝ) / (a*b) ≤ 1/6 := by rify at t3; refine one_div_le_one_div_of_le ?_ t3; linarith

  rify
  rw [h]

  suffices tar : ((a:ℝ)+b+c) ≤ (a*b*c)
  refine (one_le_div₀ ?_).mpr tar
  linarith

  have : ((a:ℝ) + b + c) / (a * b * c) = 1 / (b*c) + 1/(c*a) + 1/(a*b) := by field_simp; ring
  have : ((a:ℝ) + b + c) / (a * b * c) ≤ 1/2 + 1/3 + 1/6 := by linarith
  norm_num at this
  have : ((a:ℝ) + ↑b + ↑c) / (↑a * ↑b * ↑c) * (↑a * ↑b * ↑c) ≤ 1 * (↑a * ↑b * ↑c) := by nlinarith
  field_simp at this
  exact this