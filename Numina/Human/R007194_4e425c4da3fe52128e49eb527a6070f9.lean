import Mathlib

open Real Set

/- One line is parameterized by
\[\begin{pmatrix} 2 - 3t \\ -5 - 2t \\ 1 - 6t \end{pmatrix}.\]Another line is parameterized by
\[\begin{pmatrix} -\frac{3}{2} + s \\ 2s \\ -6 + 2s \end{pmatrix}.\]The two lines intersect at $P.$  If $\theta$ is the acute angle formed by the two lines at $P,$ then find $\cos \theta.$ -/
theorem calculus_22866 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (l1 l2 : EuclideanSpace ℝ (Fin 3)) (hl1 : l1 = ![-3, -2, -6]) (hl2 : l2 = ![1, 2, 2]) (htheta : θ = InnerProductGeometry.angle l1 l2 ∨ θ = InnerProductGeometry.angle l1 (-l2)) :
  cos θ = 19 / 21 := by
  rcases htheta with htheta | htheta
  -- $\theta$ is acute, so $\cos(\theta) > 0$
  apply congrArg (fun x ↦ cos x) at htheta
  rw [InnerProductGeometry.cos_angle] at htheta
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_three, hl1, hl2] at htheta
  have cospos : 0 < cos θ := by
    have thetain : θ ∈ Ioo (-(π / 2)) (π / 2) := by
      have subset : Ioo 0 (π / 2) ⊆ Ioo (-(π / 2)) (π / 2) := by
        refine Ioo_subset_Ioo_left ?_
        have : 0 < π := by
          exact pi_pos 
        linarith
      exact subset hθ
    exact cos_pos_of_mem_Ioo thetain
  have cosneg : cos θ < 0 := by
    rw [htheta]
    have eq : √49 * √9 = √(7 ^ 2) * √(3 ^ 2) := by
      norm_num
    rw [eq]
    simp only [eq, Nat.ofNat_nonneg, sqrt_sq]
    norm_num
  linarith
  rw [htheta, InnerProductGeometry.cos_angle]
  -- $\cos(\theta) = 19 / 21$
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_three, hl1, hl2]
  have eq : √49 * √9 = √(7 ^ 2) * √(3 ^ 2) := by
    norm_num
  simp only [eq, Nat.ofNat_nonneg, sqrt_sq]
  norm_num

