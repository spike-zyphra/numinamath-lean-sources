import Mathlib


/- 9. (16 points) In the acute triangle $\triangle ABC$, $a, b, c$ are the sides opposite to $\angle A, \angle B, \angle C$ respectively, and $a, b, c$ form an arithmetic sequence, $\sin (A-C)=\frac{\sqrt{3}}{2}$. Find $\sin (A+C)$. -/

open InnerProductGeometry
open Real
open Set
open EuclideanGeometry
open FiniteDimensional
open RealInnerProductSpace


variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

--We need to prove first some general results about sines of angles in a triangle.

--We prove that the sine of an acute angle is not zero.
lemma sinnezeroofnezero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 ∈ Ioo 0 (π/2)) : sin (∠ p1 p2 p3) ≠ 0 := by
  intro eq
  simp only [mem_Ioo] at h
  have : sin 0 = 0 := by
    simp only [sin_zero]
  rw [← this] at eq
  apply injOn_sin at eq
  · linarith
  · simp only [mem_Icc]
    exact ⟨by linarith, by linarith⟩
  · simp only [mem_Icc]
    exact ⟨by linarith, by linarith⟩

--We now prove a useful version of the law of sines that relates sines and sides of a triangle without using the circumradius. We use the theorem Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius in mathlib.
/-- **Law of sines**  -/
lemma law_of_sines (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) (p1 p2 p3 : P) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h32 : p3 ≠ p2) (hi₁ : t.points i₁ = p1) (hi₂ : t.points i₂ = p2) (hi₃ : t.points i₃ = p3) (hAacute : ∠ p2 p1 p3 ∈ Ioo 0 (π/2))  (hBacute : ∠ p3 p2 p1 ∈ Ioo 0 (π/2)) (hCacute : ∠ p1 p3 p2 ∈ Ioo 0 (π/2))  : sin (∠ p3 p2 p1) / dist p1 p3 = sin (∠ p1 p3 p2) / dist p1 p2 ∧ sin (∠ p3 p2 p1) / dist p1 p3 = sin (∠ p2 p1 p3) / dist p2 p3 := by
--We apply the theorem Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius to the angle ∠ p1 p2 p3 (i.e. B in the notation of the theorem).
  have lawsin1 := Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius t h₁₂ h₁₃ h₂₃
--We apply the theorem Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius to the angle ∠ p1 p3 p2 (i.e. C in the notation of the theorem).
  have h₃₂ : i₃ ≠ i₂ := by intro h; exact h₂₃ h.symm
  have lawsin2 := Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius t h₁₃ h₁₂ h₃₂
--We apply the theorem Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius to the angle ∠ p2 p1 p3 (i.e. A in the notation of the theorem).
  have h₂₁ : i₂ ≠ i₁ := by intro h; exact h₁₂ h.symm
  have lawsin3 := Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius t h₂₁ h₂₃ h₁₃
--We simplify the notation.
  rw [hi₁, hi₂, hi₃] at lawsin1 lawsin2 lawsin3
--We now rewrite the equalities found in terms of non-oriented angles. In particular, the absolute value of the sine of an oriented angle is equal to the sine of the corresponding non-oriented angle, since it is acute (hence the sine is positive). The following proves the result for B.
  have : |(∡ p1 p2 p3).sin| = sin (∠ p1 p2 p3) := by
    have := oangle_eq_angle_or_eq_neg_angle h12 h32
    rcases this with h | h
    all_goals
      rw [h]
      simp only [Angle.sin_neg, Angle.sin_coe, abs_neg, abs_eq_self, ge_iff_le]
      apply sin_nonneg_of_mem_Icc
      simp only [mem_Ioo, mem_Icc] at hBacute ⊢
      rw [(by rw [EuclideanGeometry.angle_comm] : ∠ p3 p2 p1 = ∠ p1 p2 p3)] at hBacute
      exact ⟨by linarith, by linarith⟩
  rw [this] at lawsin1
--We prove the same identity for C.
  have : |(∡ p1 p3 p2).sin| = sin (∠ p1 p3 p2) := by
    have h23 : p2 ≠ p3 := by intro h; exact h32 h.symm
    have := oangle_eq_angle_or_eq_neg_angle h13 h23
    rcases this with h | h
    all_goals
      rw [h]
      simp only [Angle.sin_neg, Angle.sin_coe, abs_neg, abs_eq_self, ge_iff_le]
      apply sin_nonneg_of_mem_Icc
      simp only [mem_Ioo, mem_Icc] at hCacute ⊢
      exact ⟨by linarith, by linarith⟩
  rw [this] at lawsin2
--We prove the same identity for A.
  have : |(∡ p2 p1 p3).sin| = sin (∠ p2 p1 p3) := by
    have h21 : p2 ≠ p1 := by intro h; exact h12 h.symm
    have h31 : p3 ≠ p1 := by intro h; exact h13 h.symm
    have := oangle_eq_angle_or_eq_neg_angle h21 h31
    rcases this with h | h
    all_goals
      rw [h]
      simp only [Angle.sin_neg, Angle.sin_coe, abs_neg, abs_eq_self, ge_iff_le]
      apply sin_nonneg_of_mem_Icc
      simp only [mem_Ioo, mem_Icc] at hAacute ⊢
      exact ⟨by linarith, by linarith⟩
  rw [this] at lawsin3
--We now compare the three main equalities and obtain the result.
  rw [← lawsin1, (by rw [EuclideanGeometry.angle_comm] : ∠ p1 p2 p3 = ∠ p3 p2 p1), div_eq_div_iff (sinnezeroofnezero hCacute) (sinnezeroofnezero hBacute)] at lawsin2
  rw [← lawsin1, (by rw [EuclideanGeometry.angle_comm] : ∠ p1 p2 p3 = ∠ p3 p2 p1), div_eq_div_iff (sinnezeroofnezero hAacute) (sinnezeroofnezero hBacute)] at lawsin3
  constructor
  · rw [div_eq_div_iff]
    · linarith
    · rw [dist_ne_zero]
      exact h13
    · rw [dist_ne_zero]
      exact h12
  · rw [div_eq_div_iff]
    · linarith
    · rw [dist_ne_zero]
      exact h13
    · rw [dist_ne_zero]
      intro h
      exact h32 h.symm


--We are now ready to prove the main theorem.
theorem algebra_217955 (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) (p1 p2 p3 : P) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h32 : p3 ≠ p2) (hi₁ : t.points i₁ = p1) (hi₂ : t.points i₂ = p2) (hi₃ : t.points i₃ = p3) (hAacute : ∠ p2 p1 p3 ∈ Ioo 0 (π/2))  (hBacute : ∠ p3 p2 p1 ∈ Ioo 0 (π/2)) (hCacute : ∠ p1 p3 p2 ∈ Ioo 0 (π/2)) (hapos : dist p2 p3 > 0) (hbpos : dist p1 p3 > 0) (hcpos : dist p1 p2 > 0) (hseq : ∃ d, dist p1 p3 = dist p2 p3 + d ∧ dist p1 p2 = dist p1 p3 + d) (hsin : sin (∠ p2 p1 p3 - ∠ p1 p3 p2) = sqrt 3 / 2) : sin (∠ p2 p1 p3 + ∠ p1 p3 p2) = sqrt 39 / 8 := by
--To ease the notation, we call A, B, C the angles ∠ p2 p1 p3, ∠ p3 p2 p1, ∠ p1 p3 p2 respectively, and a, b, c the sides opposite to A, B, C respectively.
  set A := ∠ p2 p1 p3 with hA
  set B := ∠ p3 p2 p1 with hB
  set C := ∠ p1 p3 p2 with hC
  set a := dist p2 p3 with ha
  set b := dist p1 p3 with hb
  set c := dist p1 p2 with hc
--Since a, b, c form an arithmetic sequence, we can write a + c = 2 * b.
  obtain ⟨d,hadb, hbdc⟩ := hseq
  have hseq' : a + c = 2 * b := by linarith
--We use the law of sines to obtain an analogous equality between the sines of the angles A, B, C, namely sin(A) + sin(C) = 2 * sin(B).
  have lawsin1 := (law_of_sines t h₁₂ h₁₃ h₂₃ p1 p2 p3 h12 h13 h32 hi₁ hi₂ hi₃ hAacute hBacute hCacute).2
  have eq_a : a = b * sin A / sin B := by
    rw [div_eq_div_iff (by linarith) (by linarith)] at lawsin1
    rw [(by simp : a = a/1), div_eq_div_iff (by linarith) (sinnezeroofnezero hBacute), mul_one]
    linarith
  have lawsin2 := (law_of_sines t h₁₂ h₁₃ h₂₃ p1 p2 p3 h12 h13 h32 hi₁ hi₂ hi₃ hAacute hBacute hCacute).1
  have eq_c : c = b * sin C / sin B := by
    rw [div_eq_div_iff (by linarith) (by linarith)] at lawsin2
    rw [(by simp : c = c/1), div_eq_div_iff (by linarith) (sinnezeroofnezero hBacute), mul_one, mul_comm, lawsin2, mul_comm]
  rw [eq_a, eq_c, mul_div_assoc, mul_div_assoc, ← mul_add, mul_comm 2] at hseq'
  simp only [mul_eq_mul_left_iff] at hseq'
  rcases hseq' with hseq' | hseq'
  swap
  linarith
  rw [← add_div, div_eq_iff_mul_eq (sinnezeroofnezero hBacute)] at hseq'
--We now use the fact that sin(A - C) = sin(π/3) to find a relation between A and C, namely A - C = π/3.
  have sinA_C : sin (A - C) = sin (π/3) := by
    rw [hsin]
    exact Eq.symm sin_pi_div_three
  have A_C : A - C = π/3 := by
    apply injOn_sin
    · simp only [mem_Icc]
      simp only [mem_Ioo] at hAacute hCacute
      exact ⟨by linarith, by linarith⟩
    · simp only [mem_Icc]
      constructor
      all_goals
        have := pi_pos
        linarith
    exact sinA_C
--Since A, B and C are the angles of a triangle, we have A + B + C = π. We can use this to find a second relation between A and C, namely A + C = π - B.
  have sumpi : A + B + C = π := by
    have := angle_add_angle_add_angle_eq_pi h12 h32
    linarith
  have A_C' : A + C = π - B := by
    rw [← sumpi]
    linarith
--Using the two relations above, we can find the values of A and C in terms of B.
  have hA' : A = π - π / 3 - B / 2 := by linarith
  have hC' : C = π / 3 - B / 2 := by linarith
--We now have a goniometric equation in B, which we can solve, finding sin(B) = √39 / 8.
  rw [hA', hC', sin_sub, sin_pi_sub, sin_pi_div_three, cos_pi_sub, cos_pi_div_three, sin_sub, sin_pi_div_three, cos_pi_div_three] at hseq'
  ring_nf at hseq'
  have : B = 2 * (B / 2) := by ring_nf
  rw [← hB] at hseq'
  nth_rw 1 [this] at hseq'
  rw [sin_two_mul] at hseq'
  ring_nf at hseq'
  rw [mul_comm, ← mul_assoc, mul_comm _ √3] at hseq'
  simp only [mul_eq_mul_right_iff] at hseq'
  rcases hseq' with hseq' | hseq'
  swap
  · rw [cos_eq_zero_iff] at hseq'
    obtain ⟨k, hk⟩ := hseq'
    have hB'' := hBacute
    simp only [mem_Ioo] at hB''
    field_simp at hk
    rw [hk] at hB''
    have := pi_pos
    obtain ⟨h1,h2⟩ := hB''
    rw [(by ring_nf : π / 2 = (1 / 2) * π), mul_lt_mul_iff_of_pos_right this] at h2
    rcases k with k | k
    · have : (1 : ℝ) ≤ 2 * (Int.ofNat k) + 1 := by
        have : 0 ≤ 2 * (Int.ofNat k) := by
          apply Int.ofNat_nonneg
        rify at this
        linarith
      linarith
    · have : (2 * (Int.negSucc k) + 1) < 0 := Int.sign_eq_neg_one_iff_neg.mp rfl
      rify at this
      have : (2 * (Int.negSucc k) + 1) * π < 0 := by
        apply mul_neg_of_neg_of_pos
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        linarith
        linarith
      linarith
  · rw [mul_comm, ← div_eq_iff_mul_eq (by linarith)] at hseq'
    have hcos : cos (B / 2) = √(1 - sin (B / 2) ^ 2) := by
      rw [cos_eq_sqrt_one_sub_sin_sq (by simp at hBacute; linarith : - (π / 2) ≤ B / 2) (by simp at hBacute; linarith : B / 2 ≤ π / 2)]
    rw [(by ring_nf : B / 2 = B * (1 / 2)), ← hseq'] at hcos
    have : (1 - (√3 / 4) ^ 2) = 13 / 16 := by
      rw [div_pow, sq_sqrt (by linarith)]
      norm_num
    rw [this] at hcos
    have hsinB : sin B = 2 * (√3 / 4) * √(13 / 16) := by
      rw [(by ring_nf : B = 2 * (B * (1 / 2))), sin_two_mul, ← hseq', hcos]
    rw [sqrt_div (by linarith), (by norm_num : (16 : ℝ) = 4 ^ 2), sqrt_sq (by linarith), (by ring_nf : 2 * (√3 / 4) * (√13 / 4) = √3 * √13 / 8),] at hsinB
    have : √3 * √13 = √39 := by
      rw [(by norm_num : (39 : ℝ) = 3 * 13), sqrt_mul (by linarith)]
    rw [this] at hsinB
--Since A + C = π - B, we can now find sin (A + C) = sin (π - B) = sin B.
    rw [A_C', sin_pi_sub]
    exact hsinB