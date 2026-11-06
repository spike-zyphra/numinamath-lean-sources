import Mathlib

/- The parabolas y=ax²−2 and y=4−bx² intersect the coordinate axes in exactly four points, and these four points are the vertices of a kite of area 12. 
What is a+b?
(A) 1
(B) 1.5
(C) 2
(D) 2.5
(E) 3 -/
theorem algebra_96472 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (p1 p2 : ℝ → ℝ) (hp1 : ∀ x, p1 x = a * x ^ 2 - 2) (hp2 : ∀x, p2 x = 4 - b * x ^ 2)
(h1 : ∃ x1 x2 y1 y2 : ℝ, x1 ≠ x2 ∧ p1 x1 = 0 ∧ p1 x2 = 0 ∧ p2 x1 = 0 ∧ p2 x2 = 0 ∧ y1 ≠ y2 ∧ p1 0 = y1 ∧ p2 0 = y2 ∧ (x2 - x1) * (y2 - y1) = 2 * 12) :
a + b = 1.5 := by
  obtain ⟨x1, x2, y1, y2, xne, hp1x1, hp1x2, hp2x1, hp2x2, yne, hp1y1, hp2y2, harea⟩:= h1
  have h1 : ∀ x, p1 x = a * x ^ 2 - 2 := by exact hp1
  have h11 : ∀ x, p1 x = a * x ^ 2 - 2 := by exact hp1
  have h12 : ∀ x, p1 x = a * x ^ 2 - 2 := by exact hp1
  have h2 : ∀x, p2 x = 4 - b * x ^ 2 := by exact hp2
  --find y1 and y2 the intercepts of the two parabolas with the y-axis
  specialize h1 0
  specialize h2 0
  ring_nf at hp1 hp2
  rw[hp1] at hp1y1
  rw[hp2] at hp2y2
  --substitute it in the fomula for the area of the kite and find the distance of x2 and x1
  rw[← hp1y1, ← hp2y2] at harea
  ring_nf at harea
  have dif : x2 - x1 = 4 := by 
    rw[← sub_mul x2 x1 6] at harea
    linarith
  --then x1=-2 and x2=2 by the fact that roots are symmetric with respect to the y-axis in those parabolas
  have k : x1 = -2 ∧ x2 = 2 := by
    specialize h11 x1
    specialize h12 x2
    rw[hp1x1] at h11
    rw[hp1x2] at h12
    rw[h11] at h12
    have eq0: a * x1^2 = a * x2^2 := by linarith
    --x1^2=x2^2
    have eq : x1^2 = x2^2 := by
      have hk := congrFun (congrArg HMul.hMul eq0) (1/a)
      simp at hk
      obtain hk1|hk2 := hk
      · exact hk1
      · contradiction
    --it implies x1=x2 or x1=-x2
    have sol : x1 = x2 ∨ x1 = - x2 := by exact sq_eq_sq_iff_eq_or_eq_neg.mp eq 
    obtain sol1|sol2 := sol
    · contradiction
    · rw[sol2] at dif
      have valx2 : x2 = 2 := by linarith
      rw[valx2] at sol2
      constructor
      · exact sol2
      · exact valx2
  -- now substitute in the equations of the parabolas to find a and b
  obtain ⟨k1,k2⟩ := k
  specialize hp1 x1
  rw[hp1x1, k1] at hp1
  ring_nf at hp1
  have haa : a = 1 / 2 := by linarith
  specialize hp2 x2
  rw[hp2x2, k2] at hp2
  have hbb : b = 1 := by linarith
  --compute a+b
  rw[haa, hbb] 
  ring_nf