import Mathlib

theorem algebra_10622 {f g : ℝ → ℝ} (hf : f = fun x => Real.sin (2 * x - Real.pi / 6)) (hg : g = fun x => Real.cos (2 * x)) :
    f = fun x => g (x - Real.pi / 3) := by
  rw [hf, hg]
  funext x
  have h1 : Real.sin (2 * x - Real.pi / 6) = Real.cos (2 * x - 2 * Real.pi / 3) := by
    have h2 : 2 * x - Real.pi / 6 = (2 * x - 2 * Real.pi / 3) + Real.pi / 2 := by 
      ring
    rw [h2]
    rw [Real.sin_add_pi_div_two]
  simp [h1]
  all_goals ring_nf <;> field_simp [Real.pi_pos]