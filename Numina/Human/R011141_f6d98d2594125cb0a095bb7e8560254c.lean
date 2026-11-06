import Mathlib

/-
5. Given that $a, b, c$ are all positive numbers, then $\min \left\{\frac{1}{a}, \frac{2}{b}, \frac{4}{c}, \sqrt[3]{a b c}\right\}$ has the maximum value of
-/
set_option maxHeartbeats 300000
theorem algebra_239398 :
IsGreatest {x | ∃a>0, ∃b>0, ∃c>0, x = min (min (min (1 / a) (2 / b)) (4 / c)) ((a * b * c) ^ ((1 : ℝ ) / 3))} (Real.sqrt 2) := by
  unfold IsGreatest
  constructor
  
  --√2 is achieved by a=√2/2, b=√2, c=2*√2.
  simp
  use (Real.sqrt 2)/2
  simp
  use (Real.sqrt 2)
  simp
  use (2*Real.sqrt 2)
  simp
  norm_num
  field_simp
  have : 4 / (2 * Real.sqrt 2) = Real.sqrt 2 := by field_simp; ring_nf; field_simp; norm_num
  rw [this]
  simp
  have : 2 = (Real.sqrt 2)^2 := by simp
  nth_rw 2 [this]
  rw [←pow_succ]
  norm_num
  have : ((Real.sqrt 2)^3)^((1:ℝ)/3) = ((Real.sqrt 2)^(3*1/3)) := by 
    rw [← Real.rpow_natCast_mul]
    simp
    positivity
  rw [this]
  simp

  --For any choice of a,b,c, the minimum value is at at most √2.
  unfold upperBounds
  dsimp
  --Let the bound be u.
  intro u hu
  obtain ⟨a,apos,b,bpos,c,cpos,h⟩ := hu
  
  have : 0 < Real.sqrt 2 := by norm_num

  by_cases unpos : u ≤ 0
  linarith

  -- We have u^3 ≤ 1/a * 2/b * 4/c, so u^3 ≤ 8 / (abc).
  -- We also know that u ≤ abc, so we get u ≤ √2, for any choice of a b c.
  have upos : 0 < u:= by linarith
  have abcpos : 0 < a * b * c := by 
    have : 0 < a*b := by nlinarith
    nlinarith
  have a1pos : 0 < 1/a := by positivity
  have b2pos : 0 < 2/b := by positivity
  have c3pos : 0 < 4/c := by positivity
  have abc13pos : 0 < (a*b*c)^((1:ℝ)/3) := by positivity

  have uabc13 : u ≤ (a * b * c) ^ ((1:ℝ) / (3:ℝ)) := by 
    rw [h]; 
    exact min_le_right (1 / a ⊓ 2 / b ⊓ 4 / c) ((a * b * c) ^ (1 / 3))
  have uabc : u ≤ 1 / a ⊓ 2 / b ⊓ 4 / c := by 
    rw [h];
    exact min_le_left (1 / a ⊓ 2 / b ⊓ 4 / c) ((a * b * c) ^ (1 / 3))
  have uc :  u ≤ 4 / c := by
    have : 1 / a ⊓ 2 / b ⊓ 4 / c ≤ 4/c := by
      exact min_le_right (1 / a ⊓ 2 / b) (4 / c)
    linarith
  have uab : u ≤ 1 / a ⊓ 2 / b := by
    have : 1 / a ⊓ 2 / b ⊓ 4 / c ≤ 1 / a ⊓ 2 / b := by
      exact min_le_left (1 / a ⊓ 2 / b) (4 / c)
    linarith
  have ub : u ≤ 2 / b := by
    have : 1 / a ⊓ 2 / b ≤ 2/b := by
      exact min_le_right (1 / a) (2 / b)
    linarith
  have ua : u ≤ 1 / a := by
    have : 1 / a ⊓ 2 / b ≤ 1 / a := by
      exact min_le_left (1 / a) (2 / b)
    linarith
  
  have ulem: u * u * u≤ (1/a) * (2/b) * (4/c) := by 
    have : u * u ≤ (1/a) * (2/b) := by nlinarith
    nlinarith
  ring_nf at ulem

  have ulem2 : u ^ 3 ≤ a*b*c := by 
    have : u*u*u ≤ (a * b * c) ^ ((1:ℝ) / 3) * (a * b * c) ^ ((1:ℝ) / 3) * (a * b * c) ^ ((1:ℝ) / 3) := by
      have : u * u  ≤ (a * b * c) ^ ((1:ℝ) / 3) * (a * b * c) ^ ((1:ℝ) / 3) := by nlinarith
      nlinarith
    ring_nf at this
    rw [← Real.rpow_mul_natCast] at this
    norm_num at this
    exact this
    linarith
  
  have u3le: u^3 ≤ 2*Real.sqrt 2 := by
    by_cases abcle22 : a*b*c ≤ 2*Real.sqrt 2
    linarith

    have abcge22 : 2*Real.sqrt 2 ≤ a*b*c := by linarith
    have : a⁻¹ * b⁻¹ * c⁻¹ ≤ (2*Real.sqrt 2)⁻¹ := by
      have : a⁻¹ * b⁻¹ * c⁻¹ = 1/(a*b*c) := by ring_nf
      rw [this]
      have : (2*Real.sqrt 2)⁻¹ = 1/(2*Real.sqrt 2) := by ring_nf
      rw [this]
      have : 0 < 2*√2 := by positivity
      exact one_div_le_one_div_of_le this abcge22
    have : u^3 ≤ (2*Real.sqrt 2)⁻¹ * 8 := by linarith
    field_simp at this
    have : 8 / (2 * √2) = 2 * √2 := by 
      field_simp
      ring_nf
      field_simp
      ring
    rw [← this]; 
    assumption

  have : 2*√2 = (√2)^3 := by 
    have : 2 = (√2)^2 := by norm_num
    nth_rw 1 [this]
    nth_rw 2 [pow_succ]
  rw [this] at u3le
  have odd3 : Odd 3 := by use 1; norm_num
  
  by_contra ug
  have : √2 < u := by linarith
  have : (√2)^3 < u^3 := by 
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr this
    linarith
    linarith
    linarith
  linarith