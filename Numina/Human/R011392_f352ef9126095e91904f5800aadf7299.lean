import Mathlib
open Finset Real
theorem algebra_24638: ∏ i ∈ Finset.range 7, cos ((i + 1) * π / 15) = 1 / 128 := by
  have cos_product_formula : ∀ n : ℕ, ∀ x : ℝ, sin x ≠ 0 →
  ∏ i ∈ range n, cos (2^i * x) = sin (2^n * x) / (2^n * sin x) := by
    intro n x hx
    induction n with
    | zero =>
      simp [hx]
    | succ n ih =>
      rw [prod_range_succ, ih]
      have h2 : sin (2 ^ (n + 1) * x) = 2 * sin (2 ^ n * x) * cos (2 ^ n * x) := by
        have h3 : sin (2 ^ (n + 1) * x) = sin (2 * (2 ^ n * x)) := by
          ring_nf
        rw [h3]
        have h4 : sin (2 * (2 ^ n * x)) = 2 * sin (2 ^ n * x) * cos (2 ^ n * x) := by
          rw [sin_two_mul]
        rw [h4]
      rw [h2]
      have h3 : (2 : ℝ) ^ (n + 1 : ℕ) = 2 * 2 ^ n := by
        ring_nf
      rw [h3]
      field_simp [hx]
      ring_nf
  have product_first : cos (π/15) * cos (2*π/15) * cos (4*π/15) * cos (8*π/15) = 
      sin (16*π/15) / (16 * sin (π/15)) := by
    have h₀ : sin (π / 15) ≠ 0 := by
      have h₁ : 0 < Real.sin (π / 15) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        <;> linarith [Real.pi_pos, Real.pi_div_two_pos]
      linarith
    have h₁ : ∏ i ∈ Finset.range 4, cos (2 ^ i * (π / 15)) = sin (2 ^ 4 * (π / 15)) / (2 ^ 4 * sin (π / 15)) := by
      apply cos_product_formula 4 (π / 15) h₀

    have h₂ : ∏ i ∈ Finset.range 4, cos (2 ^ i * (π / 15)) = cos (1 * (π / 15)) * cos (2 * (π / 15)) * cos (4 * (π / 15)) * cos (8 * (π / 15)) := by
      simp [Finset.prod_range_succ, pow_succ]
      ring_nf
    have h₃ : sin (2 ^ 4 * (π / 15)) = sin (16 * (π / 15)) := by
      norm_num [pow_succ]
    have h₄ : 2 ^ 4 = (16 : ℝ) := by norm_num
    rw [h₂, h₃, h₄] at h₁
    have h₅ : cos (1 * (π / 15)) = cos (π / 15) := by ring_nf
    have h₆ : cos (2 * (π / 15)) = cos (2 * π / 15) := by ring_nf
    have h₇ : cos (4 * (π / 15)) = cos (4 * π / 15) := by ring_nf
    have h₈ : cos (8 * (π / 15)) = cos (8 * π / 15) := by ring_nf
    rw [h₅, h₆, h₇, h₈] at h₁
    ring_nf at h₁ ⊢
    linarith

  have sin_16pi_15 : sin (16*π/15) = -sin (π/15) := by
    have h₁ : sin (16 * π / 15) = sin (π + π / 15) := by ring_nf
    rw [h₁]
    have h₂ : sin (π + π / 15) = -sin (π / 15) := by
      rw [sin_add]
      simp [sin_add, cos_add, sin_pi_div_two, cos_pi_div_two]
    rw [h₂]
  have product_first_value : cos (π/15) * cos (2*π/15) * cos (4*π/15) * cos (8*π/15) = -1/16 := by
    have h₁ : cos (π / 15) * cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) = sin (16 * π / 15) / (16 * sin (π / 15)) := by
      rw [product_first]
    rw [h₁]
    have h₂ : sin (16 * π / 15) = -sin (π / 15) := by
      rw [sin_16pi_15]
    rw [h₂]
    have h₃ : sin (π / 15) ≠ 0 := by
      have h₄ : 0 < Real.sin (π / 15) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        <;> linarith [Real.pi_pos, Real.pi_div_two_pos]
      linarith
    field_simp [h₃]
    ring_nf

  have product_second : cos (π/15) * cos (2*π/15) * cos (4*π/15) * cos (7*π/15) = 1/16 := by
    have h01: cos (7*π/15)=-cos (8*π/15):= by
      have h01 : cos (7 * π / 15) = -cos (8 * π / 15) := by
        have h₁ : cos (7 * π / 15) = cos (π - 8 * π / 15) := by ring_nf
        rw [h₁]
        have h₂ : cos (π - 8 * π / 15) = -cos (8 * π / 15) := by
          rw [cos_pi_sub]
        rw [h₂]
      rw [h01]
    rw [h01]
    linarith

  have product_third : cos (3*π/15)*cos (6*π/15) = 1/4:= by
    have h00:cos (3*π/15) * cos (6*π/15) = cos ( π / 5 ) * cos (2* π/ 5):= by ring_nf
    have h01:cos ( π / 5 ) * cos (2* π/ 5)= sin (4*π/5) / (4 * sin (π/5)):= by
      have h₀ : sin (π / 5) ≠ 0 := by
        have h₁ : 0 < Real.sin (π / 5) := by
          apply Real.sin_pos_of_pos_of_lt_pi
          <;> linarith [Real.pi_pos, Real.pi_div_two_pos]
        linarith
      have h₁ : ∏ i ∈ Finset.range 2, cos (2 ^ i * (π / 5)) = sin (2 ^ 2 * (π / 5)) / (2 ^ 2 * sin (π / 5)) := by
        apply cos_product_formula 2 (π / 5) h₀

      have h₂ : ∏ i ∈ Finset.range 2, cos (2 ^ i * (π / 5)) = cos (1 * (π / 5)) * cos (2 * (π / 5))  := by
        simp [Finset.prod_range_succ, pow_succ]
      have h₃ : sin (2 ^ 2 * (π / 5)) = sin (4 * (π / 5)) := by
        norm_num [pow_succ]
      have h₄ : 2 ^ 2 = (4 : ℝ) := by norm_num
      rw [h₂, h₃, h₄] at h₁
      have h₅ : cos (1 * (π / 5)) = cos (π / 5) := by ring_nf
      have h₆ : cos (2 * (π / 5)) = cos (2 * π / 5) := by ring_nf
      rw [h₅, h₆,] at h₁
      ring_nf at h₁ ⊢
      linarith
    have h02:sin (4*π/5) =sin (π/5) := by 
      have h21:sin (4*π/5)=sin (π- π/5) := by ring_nf 
      have h22 : sin (π- π/5) = sin (π/5) := by
        rw [sin_sub]
        simp [sin_add, cos_add, sin_pi_div_two, cos_pi_div_two]
      rw[h21,h22]
    have h03:sin (4*π/5) / (4 * sin (π/5))=1/4:= by
      rw[h02]
      have h₀ : sin (π / 5) ≠ 0 := by
        have h₁ : 0 < Real.sin (π / 5) := by
          apply Real.sin_pos_of_pos_of_lt_pi
          <;> linarith [Real.pi_pos, Real.pi_div_two_pos]
        linarith
      field_simp [h₀]
      ring_nf
    rw[h00,h01,h03]
    

  have cos_5pi_15 : cos (5*π/15) = 1/2 := by
    have h₁ : cos (5 * π / 15) = cos (π / 3) := by ring_nf
    rw [h₁]
    have h₂ : cos (π / 3) = 1 / 2 := by norm_num
    rw [h₂]

  calc ∏ i ∈ Finset.range 7, cos ((i + 1) * π / 15)
      = cos (π/15) * cos (2*π/15) * cos (3*π/15) * cos (4*π/15) * cos (5*π/15) * cos (6*π/15) * cos (7*π/15) := by
          simp [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
          ring_nf
      _ = (cos (π/15) * cos (2*π/15) * cos (4*π/15) * cos (7*π/15)) * 
          (cos (3*π/15) * cos (6*π/15)) * cos (5*π/15) := by ring
      _ = (1/16) * (1/4) * (1/2) := by rw [product_second, product_third, cos_5pi_15]
      _ = 1/128 := by norm_num