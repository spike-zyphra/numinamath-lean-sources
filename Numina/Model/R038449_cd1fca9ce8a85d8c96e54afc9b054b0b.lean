import Mathlib

theorem calculus_52493 : IsGreatest (Set.range (fun x => 25 * Real.sin (4 * x) - 60 * Real.cos (4 * x))) 65 := by
  constructor
  · -- Show that 65 is in the range of the function
    use (Real.pi - Real.arcsin (25 / 65)) / 4
    have h1 : Real.sin (4 * ((Real.pi - Real.arcsin (25 / 65)) / 4)) = 25 / 65 := by
      have h2 : 4 * ((Real.pi - Real.arcsin (25 / 65)) / 4) = Real.pi - Real.arcsin (25 / 65) := by
        ring
      rw [h2]
      have h3 : Real.sin (Real.pi - Real.arcsin (25 / 65)) = Real.sin (Real.arcsin (25 / 65)) := by
        rw [Real.sin_pi_sub]
      rw [h3]
      have h4 : Real.sin (Real.arcsin (25 / 65)) = (25 / 65 : ℝ) := by
        apply Real.sin_arcsin
        all_goals norm_num
      rw [h4]
      all_goals norm_num
    have h2 : Real.cos (4 * ((Real.pi - Real.arcsin (25 / 65)) / 4)) = - (60 / 65 : ℝ) := by
      have h2 : 4 * ((Real.pi - Real.arcsin (25 / 65)) / 4) = Real.pi - Real.arcsin (25 / 65) := by
        ring
      rw [h2]
      have h3 : Real.cos (Real.pi - Real.arcsin (25 / 65)) = - Real.cos (Real.arcsin (25 / 65)) := by
        rw [Real.cos_pi_sub]
        all_goals linarith
      rw [h3]
      have h4 : Real.cos (Real.arcsin (25 / 65)) = Real.sqrt (1 - (25 / 65) ^ 2) := by
        rw [Real.cos_arcsin]
        all_goals linarith
      rw [h4]
      have h5 : Real.sqrt (1 - (25 / 65 : ℝ) ^ 2) = (60 / 65 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h5]
      all_goals norm_num
    simp [h1, h2]
    <;> norm_num
    <;> ring_nf <;> norm_num
  · -- Show that 65 is the greatest value in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    -- We need to show that y ≤ 65
    have h_eq : y = 25 * Real.sin (4 * x) - 60 * Real.cos (4 * x) := by
      simp [hx]
      <;> tauto
    -- We need to show that $25 \sin(4x) - 60 \cos(4x) \leq 65$
    have h1 : (25 * Real.sin (4 * x) - 60 * Real.cos (4 * x)) ^ 2 ≤ 65 ^ 2 := by
      nlinarith [sq_nonneg (25 * Real.sin (4 * x) - 60 * Real.cos (4 * x)), sq_nonneg (60 * Real.sin (4 * x) + 25 * Real.cos (4 * x)), Real.sin_sq_add_cos_sq (4 * x), sq_nonneg (25 ^ 2 - 60 ^ 2)]
    -- From h1, we can deduce that $25 \sin(4x) - 60 \cos(4x) \leq 65$.
    have h2 : 25 * Real.sin (4 * x) - 60 * Real.cos (4 * x) ≤ 65 := by
      nlinarith [Real.sin_sq_add_cos_sq (4 * x), h1, sq_nonneg (25 * Real.sin (4 * x) - 60 * Real.cos (4 * x) - 65)]
    -- Now we can show that y ≤ 65
    linarith [h_eq, h2]