import Mathlib

open RealInnerProductSpace
open Real Set
open scoped BigOperators

/- The set of vectors $\mathbf{v}$ such that \[\mathbf{v} \cdot \mathbf{v} = \mathbf{v} \cdot \begin{pmatrix} 10 \\ -40 \\ 8 \end{pmatrix}\]forms a solid in space.  Find the volume of this solid. -/
theorem calculus_15083 (x : EuclideanSpace ℝ (Fin 3)) (hx : x = ![10, -40, 8])
  (sphere : Set (EuclideanSpace ℝ (Fin 3)))
  (hs : sphere = {v : EuclideanSpace ℝ (Fin 3) | ⟪v, v⟫ = ⟪v, x⟫})
  (ball_center : EuclideanSpace ℝ (Fin 3)) (hb : ball_center = ![5, -20, 4]):
  sphere = Metric.sphere ball_center 21 ∧
  MeasureTheory.volume (Metric.ball ball_center 21) = .ofReal (12348 * π) := by

  -- from the given equation, \[x^2 + y^2 + z^2 = 10x - 40y + 8z.\]Completing the square in $x,$ $y,$ and $z,$ we get \[(x - 5)^2 + (y + 20)^2 + (z - 4)^2 = 441.\]This represents the equation of a sphere with radius 21
  have hseq : sphere = Metric.sphere ball_center 21 := by
    rw [hs]
    rw [hx]
    ext v
    have hv1 : 0 ≤ (v 0 - 5) ^ 2 := by apply sq_nonneg
    have hv2 : 0 ≤ (v 1 + 20) ^ 2  := by apply sq_nonneg
    have hv3 : 0 ≤ (v 2 - 4) ^ 2  := by apply sq_nonneg
    constructor
    .
      intro hv; simp at hv; simp
      rw [hb]
      rw [EuclideanSpace.norm_eq]
      rw [sqrt_eq_iff_eq_sq]
      rw [Finset.sum]; simp; ring_nf
      repeat rw [Finset.sum] at hv; simp at hv; ring_nf at hv

      rw [show 441 - v 0 * 10 + v 0 ^ 2 + v 1 * 40 + (v 1 ^ 2 - v 2 * 8) + v 2 ^ 2 =
        v 0 ^2 + v 1 ^ 2 + v 2 ^ 2 + 441 - v 0 * 10 + v 1 * 40 - v 2 * 8 by ring_nf, hv]

      ring_nf

      rw [Finset.sum]; simp
      repeat linarith
    .
      intro hv; simp at hv; simp
      repeat rw [Finset.sum]; simp; ring_nf
      simp [hb] at hv;
      rw [EuclideanSpace.norm_eq] at hv
      rw [Finset.sum] at hv; simp at hv;
      rw [sqrt_eq_iff_eq_sq] at hv; ring_nf at hv
      apply_fun (. - 441 + v 0 * 10 - v 1 * 40 + v 2 * 8) at hv; ring_nf at hv
      exact hv
      repeat linarith

  -- its volume is \[\frac{4}{3} \pi \cdot 21^3 = \boxed{12348 \pi}.\]
  refine ⟨ hseq, ?_ ⟩
  rw [EuclideanSpace.volume_ball]
  rw [Fintype.card_fin,← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul]
  congr 1
  simp
  rw [show (3 : ℝ)/2 = 1/2 + 1 by ring_nf]
  repeat rw [Gamma_add_one]
  rw [Gamma_one_half_eq]; ring_nf
  rw [show √π = √π^(1 : ℤ) by rw [zpow_one]]
  rw [← zpow_neg]
  rw [show √π ^ (1 : ℤ) = √π by rw [zpow_one]]
  rw [show √π ^ 3 = √π ^ (3 : ℝ ) by norm_cast]
  rw [show √π ^ (-1 : ℤ) = √π ^ (-1 : ℝ) by norm_cast]
  congr 1
  rw [← Real.rpow_add]
  ring_nf
  norm_num
  rw [sq_sqrt]
  have : 0 < π := Real.pi_pos
  linarith
  have : 0 < √π := Real.sqrt_pos_of_pos pi_pos
  linarith
  repeat linarith
