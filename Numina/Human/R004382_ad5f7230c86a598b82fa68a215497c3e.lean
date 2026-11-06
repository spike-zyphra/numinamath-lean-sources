import Mathlib

open Real Set
open scoped Real

/-find the root of sqrt (2 + cos (2 * x) + sqrt 3 * tan x) / tan x = cos x + sqrt 3 * (cos x) ^ 2 / sin x-/

lemma lemma_1 {x y:ℝ} (h1:x≥0) (h:sqrt x = y) : (x=y^2)∧(y≥0) := by
  have h2 : x = y^2 := by
    calc
      x = (sqrt x) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = y^2 := by rw [h] -- Substituting $\sqrt{x} = y$ into the equation
  have h3 : y ≥ 0 := by
    have h4 : sqrt x ≥ 0 := Real.sqrt_nonneg x -- $\sqrt{x} \geq 0$ by the definition of the square root function
    linarith [h, h4] -- Substituting $\sqrt{x} = y$ and $\sqrt{x} \geq 0$ to get $y \geq 0$
  exact ⟨h2, h3⟩ -- Combining both proved facts to get the final result

lemma lemma_2 : cos (3*π/4) = -√2/2 := by
  have h1 : cos (3 * π / 4) = -√2 / 2 := by
    have h2 : 3 * π / 4 = π - π / 4 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_sub]
    have h3 : cos (π / 4) = √2 / 2 := by
      exact cos_pi_div_four
    rw [h3]
    ring
  exact h1

lemma lemma_3 : sin (3*π/4) = √2/2 := by
  have h1 : sin (3 * π / 4) = √2 / 2 := by
    have h2 : 3 * π / 4 = π - π / 4 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_sub]
    have h3 : sin (π / 4) = √2 / 2 := by
      exact sin_pi_div_four
    rw [h3]
  exact h1

lemma lemma_4 (h:√2 / 2 + √3 * (-√2 / 2) ≥ 0) : False := by
  have h1 : √2 > 0 := by positivity
  have h2 : √3 > 0 := by positivity
  have h3 : √2 / 2 + √3 * (-√2 / 2) = (√2 / 2) * (1 - √3) := by
    ring
  have h4 : √2 / 2 > 0 := by positivity
  have h5 : 1 < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have h6 : 1 - √3 < 0 := by linarith
  have h7 : (√2 / 2) * (1 - √3) < 0 := mul_neg_of_pos_of_neg h4 h6
  linarith [h3, h7, h]

lemma lemma_5 (h:-(√2 / 2) + √3 * (-√2 / 2) ≥ 0) : False := by
  have h1 : -(√2 / 2) + √3 * (-√2 / 2) < 0 := by
    have h2 : 0 < √2 := Real.sqrt_pos.2 (show (0 : ℝ) < (2 : ℝ) by norm_num)
    have h3 : 0 < √3 := Real.sqrt_pos.2 (show (0 : ℝ) < (3 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.2 (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.2 (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  linarith

lemma lemma_6 (x:ℝ) : (sin x+√3*cos x)^2=sin x^2+3*cos x^2+2*√3*sin x*cos x := by
  ring_nf
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

lemma lemma_7 : √(2 + √3) = √2 / 2 + √3 * (√2 / 2) ^ 2 / (√2 / 2) := by
  have h2 : (√2 / 2 + √3 * (√2 / 2) ^ 2 / (√2 / 2)) = (√2 + √6) / 2 := by
    have h3 : (√2 / 2) ^ 2 = 1 / 2 := by
      calc
        (√2 / 2) ^ 2 = (√2 ^ 2) / 4 := by ring
        _ = 2 / 4 := by rw [Real.sq_sqrt]; positivity
        _ = 1 / 2 := by ring
    have h4 : √3 * (√2 / 2) ^ 2 / (√2 / 2) = √3 / √2 := by
      rw [h3]
      field_simp
      <;> ring_nf <;> rw [Real.sqrt_sq] <;> positivity
    have h5 : √3 / √2 = √6 / 2 := by
      have h6 : √3 / √2 = √(3 / 2) := by
        field_simp [Real.sqrt_div]
      have h7 : √(3 / 2) = √6 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h6, h7]
    rw [h4, h5]
    field_simp
    <;> ring_nf <;> rw [Real.sq_sqrt] <;> norm_num <;> positivity
  have h9 : ((√2 + √6) / 2) ^ 2 = 2 + √3 := by
    calc
      ((√2 + √6) / 2) ^ 2 = ((√2 + √6) ^ 2) / 4 := by ring
      _ = ( (√2) ^ 2 + 2 * (√2 * √6) + (√6) ^ 2 ) / 4 := by ring
      _ = (2 + 2 * (√2 * √6) + 6) / 4 := by rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]
      _ = (8 + 2 * (√2 * √6)) / 4 := by ring
      _ = (8 + 2 * (√(2 * 6))) / 4 := by rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      _ = (8 + 2 * (√12)) / 4 := by norm_num
      _ = (8 + 2 * (2 * √3)) / 4 := by
        have h12 : √12 = 2 * √3 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h12]
      _ = (8 + 4 * √3) / 4 := by ring
      _ = 2 + √3 := by
        ring_nf
  have h11 : Real.sqrt (2 + Real.sqrt 3) = (√2 + √6) / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> (try positivity)
    <;> nlinarith [h9, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  rw [h2]
  linarith [h11]

lemma lemma_8 : √(2 + -√3) / -1 = √2 / 2 + √3 * (√2 / 2) ^ 2 / -(√2 / 2) := by
  have h1 : (√2 / 2 + √3 * (√2 / 2) ^ 2 / -(√2 / 2)) = (√2 - √6) / 2 := by
    have h3 : (√3 * (√2 / 2) ^ 2) / (-(√2 / 2)) = -√3 / √2 := by
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring
    have h4 : √2 / 2 + -√3 / √2 = (√2 - √6) / 2 := by
      have h5 : -√3 / √2 = -√6 / 2 := by
        have h6 : √6 = √2 * √3 := by
          calc
            √6 = √(2 * 3) := by norm_num
            _ = √2 * √3 := by rw [Real.sqrt_mul (by norm_num)]
        rw [h6]
        field_simp
        <;> ring_nf <;> norm_num
        <;> ring
      rw [h5]
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring
    have h2 : (√2 / 2 + √3 * (√2 / 2) ^ 2 / -(√2 / 2)) =
      √2 / 2 + (√3 * (√2 / 2) ^ 2) / (-(√2 / 2)) := by ring
    rw [h2]
    rw [h3]
    linarith [h4]
  have h2 : √(2 + -√3) / -1 = (√2 - √6) / 2 := by
    have h3 : √(2 + -√3) = (√6 - √2) / 2 := by
      have h4 : (2 + -√3) ≥ 0 := by
        have h5 : √3 ≤ 2 := by
          rw [Real.sqrt_le_left]
          all_goals norm_num
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h5 : (√6 - √2) / 2 ≥ 0 := by
        have h6 : √6 ≥ √2 := Real.sqrt_le_sqrt (by norm_num)
        have h7 : √6 - √2 ≥ 0 := by linarith [h6]
        linarith
      have h6 : ((√6 - √2) / 2) ^ 2 = 2 + -√3 := by
        calc
          ((√6 - √2) / 2) ^ 2 = ((√6) ^ 2 + (√2) ^ 2 - 2 * (√6 * √2)) / 4 := by ring_nf
          _ = (6 + 2 - 2 * (√6 * √2)) / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          _ = (8 - 2 * (√6 * √2)) / 4 := by ring_nf
          _ = (8 - 2 * (2 * √3)) / 4 := by
            have h7 : √6 * √2 = 2 * √3 := by
              calc
                √6 * √2 = √(6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
                _ = √12 := by norm_num
                _ = √(4 * 3) := by norm_num
                _ = √4 * √3 := by rw [Real.sqrt_mul (by norm_num)]
                _ = (2 : ℝ) * √3 := by rw [show √4 = (2 : ℝ) by rw [Real.sqrt_eq_cases]; norm_num]
            rw [h7]
          _ = (8 - 4 * √3) / 4 := by ring_nf
          _ = 2 + -√3 := by field_simp; ring_nf
      rw [Real.sqrt_eq_iff_sq_eq] <;> (nlinarith [h6, h5, Real.sqrt_nonneg (2 + -√3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])
    have h4 : √(2 + -√3) / -1 = -√(2 + -√3) := by ring
    rw [h4]
    rw [h3]
    ring
  linarith [h2, h1]

theorem algebra_259139 {x : ℝ} (h1 : tan x ≠ 0) (h : 2 + cos (2 * x) + sqrt 3 * tan x ≥ 0) : sqrt (2 + cos (2 * x) + sqrt 3 * tan x) / tan x = cos x + sqrt 3 * (cos x) ^ 2 / sin x ↔ ∃ n : ℤ, x = π / 4 + 2 * π * n ∨ x = - π / 4 + 2 * π * n := by
  have h2 : sin x ≠ 0 := by
    by_contra h1
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h1]
    contradiction
  have h3 : cos x ≠ 0 := by
    by_contra h
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h]
    contradiction
  constructor
  -- Obtain the solution of the equation
  intro heq
  rw [div_eq_iff,add_mul,tan_eq_sin_div_cos,show cos x * (sin x / cos x)=sin x by field_simp [h3],show √3 * cos x ^ 2 / sin x * (sin x / cos x)=√3 * cos x by field_simp; ring] at heq
  rw [←tan_eq_sin_div_cos] at heq
  obtain ⟨h4,h5⟩ := lemma_1 h heq
  nth_rw 1 [show 2=2*(cos x^2+sin x^2)by simp] at h4
  rw [cos_two_mul',lemma_6] at h4
  have h4 : √3*tan x = 2*√3*sin x*cos x := by linarith
  rw [show 2 * √3 * sin x * cos x=√3*(2*sin x*cos x) by linarith] at h4
  rw [mul_eq_mul_left_iff] at h4
  simp at h4
  rw [tan_eq_sin_div_cos] at h4
  field_simp at h4
  have h4 : sin x*(2*cos x^2-1)=0 := by linarith
  rw [mul_eq_zero_iff_left] at h4
  have h4 : cos x= √2/2∨cos x=-√2/2 := by
    have h1 : 2 * cos x ^ 2 = 1 := by
      linarith
    have h2 : cos x ^ 2 = 1 / 2 := by
      nlinarith
    have h3 : (cos x - √2 / 2) * (cos x + √2 / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h2]
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case where $\cos(x) - \frac{\sqrt{2}}{2} = 0$
      left
      linarith
    · -- Case where $\cos(x) + \frac{\sqrt{2}}{2} = 0$
      right
      linarith
  match h4 with
  | Or.inl h4 =>
    rw [←cos_pi_div_four] at h4
    obtain ⟨n,hx⟩ := cos_eq_cos_iff.1 h4.symm
    use n
    match hx with
    | Or.inl hx =>
      apply Or.intro_left
      linarith
    | Or.inr hx =>
      apply Or.intro_right
      linarith
  | Or.inr h4 =>
    rw [←lemma_2] at h4
    obtain ⟨n,hx⟩ := cos_eq_cos_iff.1 h4.symm
    match hx with
    | Or.inl hx =>
      have hx:x=3*π/4+n*(2*π):= by linarith
      rw [hx] at h5
      rw [sin_add_int_mul_two_pi,cos_add_int_mul_two_pi] at h5
      rw [lemma_2,lemma_3] at h5
      have := lemma_4 h5
      contradiction
    | Or.inr hx =>
      have hx:x=-(3*π/4)+n*(2*π):= by linarith
      rw [hx] at h5
      rw [sin_add_int_mul_two_pi,cos_add_int_mul_two_pi] at h5
      rw [sin_neg,cos_neg] at h5
      rw [lemma_2,lemma_3] at h5
      have := lemma_5 h5
      contradiction
  exact h2
  exact h1
  -- Verify the correctness of the solution
  intro hx
  obtain ⟨n,hx⟩ := hx
  match hx with
  | Or.inl hx =>
    have hx : x = π / 4 + n*(2 * π) := by linarith
    rw [hx]
    rw [show 2*(π/4+↑n*(2*π)) = π/2+↑(2*n)*(2*π) by ring_nf; simp [pow_two]; ring]
    nth_rw 1 2 [show π / 4 + ↑n * (2 * π)=π / 4 + ↑(2*n)*π by ring_nf; simp [pow_two]; ring]
    rw [cos_add_int_mul_two_pi,sin_add_int_mul_two_pi,tan_add_int_mul_pi,cos_add_int_mul_two_pi]
    norm_num
    exact lemma_7
  | Or.inr hx =>
    have hx : x = -(π / 4) + n*(2 * π) := by linarith
    rw [hx]
    rw [show 2*(-(π/4)+↑n*(2*π)) = -(π/2)+↑(2*n)*(2*π) by ring_nf; simp [pow_two]; ring]
    nth_rw 1 2 [show -(π / 4) + ↑n * (2 * π)=-(π / 4) + ↑(2*n)*π by ring_nf; simp [pow_two]; ring]
    rw [cos_add_int_mul_two_pi,sin_add_int_mul_two_pi,tan_add_int_mul_pi,cos_add_int_mul_two_pi]
    rw [cos_neg,tan_neg,cos_neg,sin_neg]
    norm_num
    exact lemma_8
