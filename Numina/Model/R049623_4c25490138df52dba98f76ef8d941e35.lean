import Mathlib

open Real

theorem other_170420 {l : ℝ} (hl : l = 5) (t1 t2 : ℝ)
    (ht1 : t1 = 100) (ht2 : t2 = 0) (c : ℝ) (hc : c = 400)
    (lambda : ℝ) (hlans : lambda = 3.3 * 10 ^ 5) (ρm ρn : ℝ)
    (hρm : ρm = 8900) (hρn : ρn = 900) :
    (l ^ 3 * t1 - l ^ 3 * t2) / (c * (l ^ 3 / (6 * ρm) - l ^ 3 / (6 * ρn))) ≤ 0.06 := by
  rw [hl]
  rw [ht1, ht2]
  rw [hc]
  rw [hρm, hρn]
  norm_num