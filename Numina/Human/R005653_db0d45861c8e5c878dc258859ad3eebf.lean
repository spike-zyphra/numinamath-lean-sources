import Mathlib

open Complex EuclideanGeometry

/-Let $\omega$ be a circle, and let $A B C D$ be a quadrilateral inscribed in $\omega$. Suppose that $B D$ and $A C$ intersect at a point $E$. The tangent to $\omega$ at $B$ meets line $A C$ at a point $F$, so that $C$ lies between $E$ and $F$. Given that $A E=6, E C=4, B E=2$, and $B F=12$, find $D A$.-/
theorem geometry_609262 {A B C D E F O : ℂ} {r : ℝ} (rpos : 0 < r)
    (impos : 0 < A.im ∧ 0 < C.im ∧ 0 < D.im)
    (hO : O = r * I) (hB : B = 0) (hF : F = 12)
    (hA : dist A O = r) (hC : dist C O = r)
    (hD : dist D O = r) (hE : ∠ A E C = Real.pi ∧ ∠ D E B = Real.pi)
    (Cbtw1 : ∠ E C F = Real.pi) (Cbtw2 : ∠ A C F = Real.pi) (d1 : dist A E = 6)
    (d2 : dist E C = 4) (d3 : dist B E = 2) : dist D A = 2 * √42 := by
-- Prove that $A$ is not equal to $C$
  have AneC : A ≠ C := by
    intro h; rw [h, dist_comm] at d1
    linarith only [d1, d2]
-- Extend the assumption `hE` and `impos`
  rcases hE with ⟨hE1, hE2⟩; rw [angle_comm] at hE2
  rcases impos with ⟨imApos, imCpos, imDpos⟩
  have cosph : Cospherical {A, C, B, D} := by
    use O, r; simp [hA, hB, hC, hD]
    simp [hO]; positivity
-- Apply Intersecting Chords Theorem to chords $AC$ and $BD$, then compute the length of $DE$
  have ICE := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi cosph hE1 hE2
  rw [d1, dist_comm, d2, d3] at ICE; norm_num at ICE
  rw [mul_comm, ← div_eq_iff] at ICE; norm_num at ICE
  rw [angle_comm] at hE1
  have VAE := angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hE1 hE2
  rw [angle_comm] at VAE; rw [dist_comm] at d2
-- Since triangles $AED$ and $BEC$ are similar, we can show $AD=3*BC$
  have sim := dist_mul_of_eq_angle_of_dist_mul A E D B E C (1/3) VAE
  rw [d3, d1, d2, ← ICE] at sim; norm_num at sim
  rw [one_div_mul_eq_div, eq_div_iff] at sim
  rw [dist_comm, ← sim, ← eq_div_iff]
-- Denote $X$ and $Y$ to be the following two points, they are given by the intersections of line $FO$ with the circle
  let X := 12 * r / √(r ^ 2 + 144) + (r - r ^ 2 / √(r ^ 2 + 144))* I
  let Y := -12 * r / √(r ^ 2 + 144) + (r + r ^ 2 / √(r ^ 2 + 144)) * I
-- Prove that $X$ is not equal to $Y$
  have XneY : X ≠ Y := by
    intro h; simp [Complex.ext_iff, X, Y] at h
    norm_cast at h; simp at h
    rw [div_eq_iff, div_mul_cancel₀] at h
    linarith only [rpos, h.left]
    all_goals positivity
-- Prove that $A$, $C$, $X$ and $Y$ are cospherical
  have cosp' : Cospherical {A, C, X, Y} := by
    use O, r; simp [hA, hC]; constructor
    · simp [dist_eq, abs_eq_sqrt_sq_add_sq]
      rw [Real.sqrt_eq_iff_eq_sq, hO]; dsimp [X]
      simp; norm_cast; simp
      rw [div_pow, div_pow, div_add_div_same]
      rw [Real.sq_sqrt, show (12*r)^2+(r^2)^2 = r^2*(r^2+144) by ring]
      rw [mul_div_cancel_right₀]; all_goals positivity
    simp [dist_eq, abs_eq_sqrt_sq_add_sq]
    rw [Real.sqrt_eq_iff_eq_sq, hO]; dsimp [Y]
    simp; norm_cast; simp
    rw [div_pow, div_pow, div_add_div_same]
    rw [Real.sq_sqrt, show (-(12*r))^2+(r^2)^2 = r^2*(r^2+144) by ring]
    rw [mul_div_cancel_right₀]; all_goals positivity
-- Prepare to use Intersecting Secants Theorem `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`
  have ISFaux1 : ∠ A F C = 0 := by
    rw [angle_eq_pi_iff_sbtw] at Cbtw2
    exact Cbtw2.angle₁₃₂_eq_zero
  have ISFaux2 : ∠ X F Y = 0 := by
    simp [angle, X, Y, hF]
    rw [InnerProductGeometry.angle_eq_zero_iff]; constructor
    · simp [Complex.ext_iff]; norm_cast; simp
      rw [sub_eq_zero]; intro h; symm at h
      rw [eq_div_iff, mul_right_inj', Real.sqrt_eq_iff_eq_sq] at h
      simp at h; all_goals positivity
    simp [Complex.ext_iff]; norm_cast; simp
    use (√(r^2+144)+r)/(√(r^2+144)-r); split_ands
    · apply div_pos; positivity
      rw [sub_pos, Real.lt_sqrt]; simp
      all_goals positivity
    · field_simp; rw [eq_div_iff]; ring
      suffices : 0 < (√(r ^ 2 + 144) - r) * √(r ^ 2 + 144)
      · linarith only [this]
      apply mul_pos; rw [sub_pos, Real.lt_sqrt]; simp
      all_goals positivity
    field_simp; rw [eq_div_iff]; ring
    suffices : 0 < (√(r ^ 2 + 144) - r) * √(r ^ 2 + 144)
    · linarith only [this]
    apply mul_pos; rw [sub_pos, Real.lt_sqrt]; simp
    all_goals positivity
-- Apply Intersecting Secants Theorem to $AC$ and $XY$ intersecting at $F$
  have ISF := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero cosp' AneC XneY ISFaux1 ISFaux2
-- Compute the product of $XF$ and $YF$
  have : dist X F * dist Y F = 144 := by
    simp [dist_eq, abs_eq_sqrt_sq_add_sq]
    rw [← Real.sqrt_mul, Real.sqrt_eq_iff_eq_sq]
    simp [X, Y, hF]; norm_cast; field_simp; ring_nf
    rw [show √(144+r^2)^4 = (√(144+r^2)^2)^2 by ring, Real.sq_sqrt]
    ring; all_goals positivity
  rw [this, (dist_eq_add_dist_iff_angle_eq_pi _ _).mpr Cbtw2] at ISF
  replace this : dist A C = 10 := by
    rw [show (10:ℝ) = 6+4 by norm_num, ← d1, ← d2]
    rw [dist_eq_add_dist_iff_angle_eq_pi, angle_comm]
    exact hE1; intro h; simp [h] at d1
    intro h; simp [h] at d2
  rw [this, dist_comm, ← sub_eq_zero] at ISF
-- Solve for $CF$ from the equation
  simp [show (10+dist C F)*dist C F-144 = (dist C F-8)*(dist C F+18) by ring] at ISF
  rw [or_comm] at ISF; rcases ISF with h|ISF
  · suffices : 0 < dist C F + 18
    · linarith [this, h]
    positivity
  rw [sub_eq_zero] at ISF; rw [angle_comm] at Cbtw1
  rw [dist_comm] at d2 ISF; replace this : dist E F = 12 := by
    rw [show (12:ℝ) = 8+4 by norm_num, ← ISF, ← d2, add_comm]
    rw [dist_eq_add_dist_iff_angle_eq_pi, angle_comm]
    exact Cbtw1; intro h; simp [h] at d2
    intro h; simp [h] at ISF
-- Apply Stewart's Theorem `dist_sq_mul_dist_add_dist_sq_mul_dist` to triangle $BFE$ and point $C$, then solve for $BC$, the goal follows
  have ST := dist_sq_mul_dist_add_dist_sq_mul_dist B F E C Cbtw1
  rw [d2, d3, ISF, show dist B F = 12 by simp [hB, hF]] at ST
  rw [dist_comm, this] at ST
  replace ST : dist B C ^ 2 = (2 * √42 / 3) ^ 2 := by
    rw [div_pow, mul_pow]; norm_num; linarith only [ST]
  rw [pow_left_inj₀] at ST; exact ST
  any_goals positivity
  exact AneC; intro h; simp [h] at Cbtw1
  linarith only [Real.pi_pos, Cbtw1]