import Mathlib

theorem algebra_12951 {f g : ℝ → ℝ} (hf : f = fun x => 4.125 - (x + 0.5)^2 / 2)
    (hg : g = fun x => f (x - 3)) (x : ℝ) (hx : f x = g x) :
    x + f x = 4 := by
  have g_def : g x = f (x - 3) := by
    rw [hg]
  rw [g_def] at hx
  rw [hf] at hx
  simp at hx
  have hx_eq : x = 1 := by
    nlinarith
  have hfx_val : f x = 3 := by
    rw [hf]
    rw [hx_eq]
    norm_num
  linarith [hx_eq, hfx_val]