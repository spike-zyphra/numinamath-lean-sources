import Mathlib

/- # 3. (10 points) Determine the sign of the expression

$\sqrt{25 \sqrt{7}-27 \sqrt{6}}-\sqrt{17 \sqrt{5}-38} \quad$ or
-/
theorem algebra_260925 : (Real.sqrt (25 * Real.sqrt 7 - 27 * Real.sqrt 6) - Real.sqrt (17 * Real.sqrt 5 - 38)) < 0 := by
  -- an auxilary lemma that (√x)^3 = x * √x
  have sqrt_cube (x: ℝ) (h: 0 ≤ x) : (√x)^3 = x * √x := by
    nth_rw 2 [← @Real.mul_self_sqrt x h]
    ring
  -- express (25√7-27√6) as a cube
  have : (√7 - √6)^3 = 25*√7-27*√6 := by
    ring_nf
    simp [sqrt_cube]
    ring
  rw [← this]
  -- express (17√5-38) as a cube
  have : (√5 - 2)^3 = 17*√5-38 := by
    ring_nf
    simp [sqrt_cube]
    ring
  rw [← this]
  -- prove √7 + 2 < √5 + √6, this will mean √7-√6 < √5 - 2 which will prove the target as targets are just √(x^3) for x = √7-√6, √5-2
  have : √7 + 2 < √5 + √6 := by
    apply (sq_lt_sq₀ (by positivity: √7 + 2 ≥ 0) (by positivity: √5 + √6 ≥ 0)).mp
    ring_nf
    simp
    rw [← Real.sqrt_mul (by norm_num)]
    ring_nf
    apply add_lt_add_left
    apply (sq_lt_sq₀ (by positivity: √7 * 4 ≥ 0) (by positivity: √30 * 2 ≥ 0)).mp
    ring_nf
    simp
    norm_num
  have : √6 < √7 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have : √7 - √6 > 0 := by linarith
  have : √((√7 - √6)^3) < √((√5 - 2)^3) := by
    apply Real.sqrt_lt_sqrt
    . positivity
    . refine pow_lt_pow_left₀ ?_ ?_ ?_
      . linarith
      . positivity
      . norm_num
  linarith