import Mathlib

theorem algebra_13529 {A B : ℝ} (hB : B ≠ 0) (f g : ℝ → ℝ)
    (hf : f = fun x => A * x - 2 * B ^ 2) (hg : g = fun x => B * x)
    (hfg : f (g 1) = 0) : A = 2 * B := by
  -- calculate g 1
  have g1_val : g 1 = B := by
    rw [hg]
    norm_num
  rw [g1_val] at hfg
  rw [hf] at hfg
  simp at hfg
  -- get identity
  have eq1 : A * B - 2 * B^2 = 0 := by linarith
  have eq2 : A * B = 2 * B^2 := by linarith [eq1]
  -- solve
  have h1 : A * B - 2 * B^2 = 0 := by linarith
  have h2 : B * (A - 2 * B) = 0 := by
    linarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case h3: $B = 0$
    exfalso
    exact hB (by linarith)
  · -- Case h4: $A - 2 * B = 0$
    linarith