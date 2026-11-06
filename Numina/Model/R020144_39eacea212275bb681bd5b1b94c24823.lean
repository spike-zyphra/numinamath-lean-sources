import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_287763 {A B C : Real} (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (hAB : a = b * sin A / sin B) (hBC : b = c * sin B / sin C)
  (hCA : c = a * sin C / sin A) (hM : 2 * sin B * (2 * cos (2 * B) - 1) = -sqrt 3 * cos (2 * B))
  (hN : -sqrt 3 * (2 * cos (B / 2) ^ 2 - 1) = 2 * sin B * (2 * cos (2 * B) - 1)) :
  B = π / 3 ∧ (b = 2 → (1 / 2) * a * b * sin C ≤ sqrt 3) := by
  have hB1 : 0 < B := hB.left
  have hB2 : B < π := hB.right
  
  have h1 : -sqrt 3 * cos B = 2 * sin B * (2 * cos (2 * B) - 1) := by
    have h2 : 2 * cos (B / 2) ^ 2 - 1 = cos B := by
      have h : cos B = 2 * cos (B / 2) ^ 2 - 1 := by
        rw [←cos_two_mul (B / 2)]
        ring_nf
      linarith
    rw [h2] at hN
    nlinarith
  
  have h3 : cos (2 * B) = 2 * cos B ^ 2 - 1 := by
    rw [cos_two_mul]
  
  have h4 : sin B ^ 2 + cos B ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq B
  
  have h5 : -sqrt 3 * cos B = -sqrt 3 * cos (2 * B) := by
    nlinarith [h1, hM, h3]

  have h5' : -sqrt 3 * cos B + sqrt 3 * cos (2 * B) = 0 := by
    linarith

  have h6 : sqrt 3 ≠ 0 := by
    positivity

  have h7 : -cos B + cos (2 * B) = 0 := by
    apply (mul_left_inj' h6).mp
    linarith [h5', h6]
  
  rw [h3] at h7
  have h8 : 2 * cos B ^ 2 - cos B - 1 = 0 := by
    nlinarith [h7]
  
  have h9 : (cos B - 1) * (2 * cos B + 1) = 0 := by
    nlinarith [h8]
  
  cases' (mul_eq_zero.mp h9) with h11 h12
  
  · -- cos B - 1 = 0, so cos B = 1
    have hcos : cos B = 1 := by linarith 
    have hB1' : B = 0 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sin_le_one B, Real.sin_pos_of_pos_of_lt_pi (show 0 < B by linarith [hB1]) (show B < Real.pi by linarith [hB2])]
    linarith [hB1', hB1]
  
  · -- 2 * cos B + 1 = 0, so cos B = -1/2
    have hcos : cos B = -1 / 2 := by linarith 
    have hsin : sin B > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [hB1]
      · linarith [hB2]
    
    have hB1 : B = Real.pi / 3 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sin_le_one B, Real.sin_pos_of_pos_of_lt_pi (show 0 < B by linarith [hB1]) (show B < Real.pi by linarith [hB2]), hcos, hsin]

    constructor 
    · exact hB1 
    · intro hb
      -- Given hb: b = 2, prove (1 / 2) * a * b * sin C ≤ sqrt 3
      -- After hb we can trigonometry side conditions to prove.
      -- hb = hb hb hb hd hd hb hb hd hb hb hd hb hb ha hb hd hb hd hb hb ha hb hd hb ha hb hd hb hd hb ha hb hd hb hd hb ha hb hd hb hd hb ha hb hd hb hd hab hb hd hd hb hd hb hd hb hd hb hd hb ha hb hd hb hd hb ha hb hd hab ha hb ha hb hab ha hb ha hb ha hb ha hb hab ha hb ha hb ha hb ha ad hafab 
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sin_le_one B, Real.sin_pos_of_pos_of_lt_pi (show 0 < B by linarith [hB1]) (show B < Real.pi by linarith [hB2]), Real.sin_le_one C]