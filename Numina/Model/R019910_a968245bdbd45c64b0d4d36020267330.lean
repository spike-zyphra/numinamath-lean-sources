import Mathlib

theorem algebra_201235 (f : ℝ → ℝ) (hf : f = fun x => Real.sin x + Real.sqrt 3 * Real.cos x) :
    IsGreatest (Set.range f) 2 := by
  have h1 : ∀ x, f x = Real.sin x + Real.sqrt 3 * Real.cos x := by
    intro x
    rw [hf]

  constructor
  · -- Show 2 is in the range
    use Real.pi / 6
    have h2 : f (Real.pi / 6) = 2 := by
      rw [h1]
      have hsin : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
      have hcos : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        have h : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
          exact Real.cos_pi_div_six
        linarith
      rw [hsin, hcos]
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    linarith [h2]
  · -- Show no greater value is in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h1 x] at hx
    have h2 : (Real.sin x + Real.sqrt 3 * Real.cos x) ≤ 2 := by
      have h3 : Real.sin x + Real.sqrt 3 * Real.cos x = 2 * Real.sin (x + Real.pi / 3) := by
        have h31 : Real.sin (x + Real.pi / 3) = Real.sin x * Real.cos (Real.pi / 3) + Real.cos x * Real.sin (Real.pi / 3) := by
          rw [Real.sin_add]
        have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
        have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        rw [h4, h5] at h31
        rw [h31]
        ring_nf
      have h4 : Real.sin (x + Real.pi / 3) ≤ 1 := by
        apply Real.sin_le_one
      linarith [h3, h4]
    linarith [h2, hx]