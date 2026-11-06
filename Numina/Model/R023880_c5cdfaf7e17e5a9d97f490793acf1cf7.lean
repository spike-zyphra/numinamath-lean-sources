import Mathlib

open Real

theorem inequalities_46877 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    min (min (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) ≤ 1 / 4 ∧
    max (max (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) ≥ 2 / 9 := by
  constructor
  · -- Prove min ≤1/4
    by_contra h1
    push_neg at h1
    have h2 : a * (1 - b) > 1 / 4 := by 
      have h3 : a * (1 - b) ≥ min (min (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [min_le_iff]
      nlinarith
    have h3 : b * (1 - c) > 1 / 4 := by 
      have h4 : b * (1 - c) ≥ min (min (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [min_le_iff]
      nlinarith
    have h4 : c * (1 - a) > 1 / 4 := by 
      have h5 : c * (1 - a) ≥ min (min (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [min_le_iff]
      nlinarith
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  · -- Prove $\max\{a(1-b),b(1-c),c(1-a)\}\geq \frac{2}{9}$
    by_contra h2
    push_neg at h2
    have h1 : a * (1 - b) < 2 / 9 := by 
      have h4 : a * (1 - b) ≤ max (max (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [le_max_iff]
      nlinarith
    have h2 : b * (1 - c) < 2 / 9 := by 
      have h5 : b * (1 - c) ≤ max (max (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [le_max_iff]
      nlinarith
    have h3 : c * (1 - a) < 2 / 9 := by 
      have h6 : c * (1 - a) ≤ max (max (a * (1 - b)) (b * (1 - c))) (c * (1 - a)) := by 
        simp [le_max_iff]
      nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]