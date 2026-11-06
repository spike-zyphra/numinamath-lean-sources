import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12188 {f g : ℝ → ℝ}
  (hf : f = λ x => sin (π * x / 4 - π / 6) - 2 * (cos (π * x / 8))^2 + 1)
  (hg : ∀ x, g (1 + x) = f (1 - x)) :
  IsGreatest (image g (Icc 0 (4 / 3))) (Real.sqrt 3 / 2) := by
  have h1 : ∀ x, g x = f (2 - x) := by
    intro x
    have eq1 := hg (x - 1)
    rw [show 1 + (x - 1 : ℝ) = x by ring] at eq1
    rw [show 1 - (x - 1 : ℝ) = (2 - x : ℝ) by ring] at eq1
    linarith
  have h2 : ∀ x, f x = sin (π * x / 4 - π / 6) - 2 * (cos (π * x / 8))^2 + 1 := by
    intro x
    rw [hf]
  have h3 : g 0 = Real.sqrt 3 / 2 := by
    have h4 : g 0 = f 2 := by
      specialize h1 0
      norm_num at h1 ⊢
      linarith
    rw [h4]
    rw [h2 2]
    have h5 : sin (π * (2: ℝ) / 4 - π / 6) = sin (π / 3) := by 
      ring_nf
    have h6 : cos (π * (2: ℝ) / 8) = cos (π / 4) := by
      ring_nf
    rw [h5, h6]
    have h7 : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    have h8 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [h7, h8]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  constructor
  · -- Show that Real.sqrt 3 / 2 is in the image of g on [0, 4/3]
    rw [mem_image]
    use 0
    constructor
    · -- Show that 0 is in [0, 4/3]
      exact ⟨by linarith, by linarith⟩
    · -- Show that g(0) = Real.sqrt 3 / 2
      exact h3
  · -- Show that Real.sqrt 3 / 2 is an upper bound
    intro y hy
    rcases hy with ⟨x, hx, h9⟩
    rw [mem_Icc] at hx
    have hx1 : 0 ≤ x := hx.1
    have hx2 : x ≤ 4 / 3 := hx.2
    have h10 : g x = f (2 - x) := h1 x
    rw [h10] at h9
    have h11 : f (2 - x) = Real.sqrt 3 * sin ((π * (2 - x) / 4 - π / 3)) := by 
      rw [h2 (2 - x)]
      have h_eq : sin (π * (2 - x) / 4 - π / 6) - 2 * (cos (π * (2 - x) / 8))^2 + 1 = Real.sqrt 3 * sin ((π * (2 - x) / 4 - π / 3)) := by
        have h12 : cos (π * (2 - x) / 8) ^ 2 = (1 + cos (π * (2 - x) / 4)) / 2 := by 
          have h13 : cos (π * (2 - x) / 4) = 2 * cos (π * (2 - x) / 8) ^ 2 - 1 := by 
            rw [←Real.cos_two_mul (π * (2 - x) / 8)]
            ring_nf
          nlinarith
        rw [h12]
        have h14 : sin (π * (2 - x) / 4 - π / 6) = (Real.sqrt 3 / 2) * sin (π * (2 - x) / 4) - (1 / 2) * cos (π * (2 - x) / 4) := by 
          rw [show π * (2 - x) / 4 - π / 6 = π * (2 - x) / 4 - π / 6 by ring]
          rw [show π * (2 - x) / 4 - π / 6 = (π * (2 - x) / 4) - (π / 6) by ring]
          rw [Real.sin_sub]
          have hsin : sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
          have hcos : cos (π / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
          simp [hsin, hcos]
          <;> ring_nf <;> simp
        rw [h14]
        have h15 : cos (π * (2 - x) / 4) = cos (π * (2 - x) / 4) := by ring_nf
        have h16 : sin (π * (2 - x) / 4 - π / 3) = sin (π * (2 - x) / 4) * cos (π / 3) - cos (π * (2 - x) / 4) * sin (π / 3) := by 
          rw [show π * (2 - x) / 4 - π / 3 = π * (2 - x) / 4 - π / 3 by ring]
          rw [Real.sin_sub]
        rw [h16]
        have hsin3 : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
        have hcos3 : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        rw [hsin3, hcos3]
        <;> nlinarith [Real.sin_sq_add_cos_sq (π * (2 - x) / 4), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sin (π * (2 - x) / 4) - Real.sqrt 3 / 2), sq_nonneg (cos (π * (2 - x) / 4) + 1 / 2), Real.sin_sq_add_cos_sq (π * (2 - x) / 4), Real.sqrt_nonneg 3]
      linarith
    rw [h11] at h9
    have h13 : -(Real.pi / 6) ≤ π * (2 - x) / 4 - Real.pi / 3 := by
      nlinarith [Real.pi_pos, hx1]
    have h14 : π * (2 - x) / 4 - Real.pi / 3 ≤ Real.pi / 6 := by
      nlinarith [Real.pi_pos, hx2]
    have h15 : sin ((π * (2 - x) / 4 - Real.pi / 3)) ≤ 1 / 2 := by
      have h12 : -(Real.pi / 6) ≤ π * (2 - x) / 4 - Real.pi / 3 := h13
      have h13 : π * (2 - x) / 4 - Real.pi / 3 ≤ Real.pi / 6 := h14
      have h16 : sin ((π * (2 - x) / 4 - Real.pi / 3)) ≤ sin (Real.pi / 6) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals
          nlinarith [Real.pi_pos]
      have h17 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
      linarith
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sin_sq_add_cos_sq (π * (2 - x) / 4 - Real.pi / 3), h15, Real.sqrt_nonneg 3]