import Mathlib

theorem inequalities_278111 (a b : Fin 3 → ℝ)
    (ha : ∀ i j, i < j → a i ≥ a j)
    (hb : ∀ i j, i < j → b i ≥ b j)
    (hpos : ∀ i, a i > 0 ∧ b i > 0)
    (hprod : a 0 * a 1 * a 2 = b 0 * b 1 * b 2)
    (hdiff : a 0 - a 2 ≤ b 0 - b 2) :
    a 0 + a 1 + a 2 ≤ 2 * (b 0 + b 1 + b 2) := by
  have ha01 : a 0 > 0 := (hpos 0).left 
  have ha11 : a 1 > 0 := (hpos 1).left 
  have ha21 : a 2 > 0 := (hpos 2).left 
  have hb01 : b 0 > 0 := (hpos 0).right
  have hb11 : b 1 > 0 := (hpos 1).right
  have hb21 : b 2 > 0 := (hpos 2).right
  have h1 : a 0 ≥ a 1 := by 
    apply ha 0 1 
    all_goals simp 
  have h2 : a 1 ≥ a 2 := by 
    apply ha 1 2 
    all_goals simp 
  have h3 : b 0 ≥ b 1 := by 
    apply hb 0 1 
    all_goals simp 
  have h4 : b 1 ≥ b 2 := by 
    apply hb 1 2 
    all_goals simp 
  have h5 : a 0 - a 2 ≤ b 0 - b 2 := hdiff
  have h5a : a 0 * a 1 * a 2 = b 0 * b 1 * b 2 := hprod
  nlinarith [ 
    mul_nonneg (show (0 : ℝ) ≤ a 0 - a 1 from by linarith) (show (0 : ℝ) ≤ a 1 - a 2 from by linarith), 
    mul_nonneg (show (0 : ℝ) ≤ a 1 - a 2 from by linarith) (show (0 : ℝ) ≤ a 2 by linarith), 
    mul_nonneg (show (0 : ℝ) ≤ b 0 - b 1 from by linarith) (show (0 : ℝ) ≤ b 1 - b 2 from by linarith), 
    mul_nonneg (show (0 : ℝ) ≤ a 0 - a 2 from by linarith) (show (0 : ℝ) ≤ b 0 - b 2 from by linarith), 
    mul_pos ha01 ha11, mul_pos ha01 ha21, mul_pos ha11 ha21, 
    mul_pos hb01 hb11, mul_pos hb01 hb21, mul_pos hb11 hb21, 
    mul_pos (show 0 < a 0 from by linarith) (show 0 < b 0 from by linarith), 
    mul_pos (show 0 < a 1 from by linarith) (show 0 < b 1 from by linarith), 
    mul_pos (show 0 < a 2 from by linarith) (show 0 < b 2 from by linarith)
  ]