import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

-- Using the namespace for Euclidean Geometry is convenient

open Real InnerProductSpace
open scoped EuclideanGeometry-- Open namespaces for Real numbers and Inner Product Space operations

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
                                                                 [MetricSpace P] [NormedAddTorsor V P]

namespace Geom_605768

lemma distinct_points_triangle (t : Affine.Triangle ℝ P) :
    (t.points 0 ≠ t.points 1) ∧ (t.points 1 ≠ t.points 2) ∧ (t.points 2 ≠ t.points 0) := by
 -- Use the fact that the points are affinely independent
  have h01 : t.points 0 ≠ t.points 1 := by
    intro h
    apply  AffineIndependent.injective t.independent at h
    contradiction
  have h12 : t.points 1 ≠ t.points 2 := by
    intro h
    apply  AffineIndependent.injective t.independent at h
    contradiction
  have h20 : t.points 2 ≠ t.points 0 := by
    intro h
    apply  AffineIndependent.injective t.independent at h
    contradiction

  refine ⟨h01, h12, h20⟩
lemma dist_side_triangle_pos (t : Affine.Triangle ℝ P) :
    0 < dist (t.points 0)  (t.points 1) ∧ 0 < dist (t.points 1)  (t.points 2) ∧
    0 < dist (t.points 2)  (t.points 0) := by
 -- Use the fact that the points are affinely independent
  obtain ⟨h01, h12, h20⟩ := distinct_points_triangle t
  refine' ⟨_,_,_⟩
  ·
    exact dist_pos.mpr h01
  ·
    exact dist_pos.mpr h12
  ·
    exact dist_pos.mpr h20


lemma two_triangles_simil ( t1 t2 : Affine.Triangle ℝ P )
    (h1 : ∠ (t1.points 0) (t1.points 1) (t1.points 2) = π / 2)
    (h2 : ∠ (t2.points 0) (t2.points 1) (t2.points 2) = π / 2)
    (heq_angle : ∠ (t1.points 1) (t1.points 2) (t1.points 0) =  ∠ (t2.points 1) (t2.points 2) (t2.points 0) )
    :
    dist (t1.points 1) (t1.points 2) * dist (t2.points 2) (t2.points 0) =
    dist (t1.points 2) (t1.points 0) * dist (t2.points 1) (t2.points 2) := by

   have h11 := EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two  h1

   obtain ⟨dist_01,dist_12,dist_20⟩ := dist_side_triangle_pos t1
   rw[dist_comm] at dist_20
   have distnz_1 := (ne_of_lt (dist_20)).symm
   have h12 := EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two  h2

   obtain ⟨dist_01,dist_12,dist_20⟩ := dist_side_triangle_pos t2
   rw[dist_comm] at dist_20
   have distnz_2 := (ne_of_lt (dist_20)).symm
   have h12 := EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two  h2

   have h11_a := (@mul_inv_eq_iff_eq_mul₀ ℝ  _
       (dist (t1.points 2) (t1.points 1)  )
       ( dist (t1.points 0) (t1.points 2 ) ) ( cos ( ∠ (t1.points 1) (t1.points 2) (t1.points 0)))
       distnz_1 ).mpr  h11.symm

   have h12_a := (@mul_inv_eq_iff_eq_mul₀ ℝ  _
       (dist (t2.points 2) (t2.points 1)  )
       ( dist (t2.points 0) (t2.points 2 ) ) ( cos ( ∠ (t2.points 1) (t2.points 2) (t2.points 0)))
       distnz_2 ).mpr  h12.symm
   rw [heq_angle] at h11_a
   have htr := Eq.trans h11_a h12_a.symm
   rw[← div_eq_mul_inv, ← div_eq_mul_inv] at htr
   have hmul := (@mul_eq_mul_of_div_eq_div ℝ _ (dist (t1.points 0) (t1.points 2))
      (dist (t2.points 0) (t2.points 2 )) (dist (t1.points 2) (t1.points 1)  )
      (dist (t2.points 2) (t2.points 1)    ) distnz_1 distnz_2) htr

   nth_rewrite 1 [dist_comm] at  hmul
   nth_rewrite 2 [dist_comm] at  hmul
   nth_rewrite 3 [dist_comm] at  hmul
   nth_rewrite 4 [dist_comm] at  hmul

   nth_rewrite 2 [mul_comm] at  hmul
   exact hmul


lemma ineq_3_nr (a b c : ℝ) : a*b + b*c + c*a <= a*a + b * b + c*c := by
  suffices 2 * (a*b + a*c + b*c) <= 2 * (a*a + b*b + c*c) by linarith  -- Deduce original inequality by dividing by 2
  -- Now prove 2*LHS <= 2*RHS
  rw [← sub_nonneg] -- Goal: 0 ≤ 2 * (a*a + b*b + c*c) - 2 * (a*b + a*c + b*c)
  calc 0
    _ ≤ (a - b)^2 + (a - c)^2 + (b - c)^2 := by positivity
    _ = 2 * a*a + 2 * b*b + 2 * c*c - (2 * a*b + 2 * a*c + 2 * b*c) := by ring
    _ = 2 * (a*a + b*b + c*c) - 2 * (a*b + a*c + b*c) := by ring

end Geom_605768

open Geom_605768


theorem Geom_605768 (tHEA tCDA tHFA tBDA
                     tHFB tAEB tHDB tCEB
                     tHEC tAFC tHDC tBFC
                     tABC :Affine.Triangle ℝ P)
    (h1 : ∠ (tHEA.points 0) (tHEA.points 1) (tHEA.points 2) = π / 2)
    (h2 : ∠ (tCDA.points 0) (tCDA.points 1) (tCDA.points 2) = π / 2)
    (h3 : ∠ (tHFA.points 0) (tHFA.points 1) (tHFA.points 2) = π / 2)
    (h4 : ∠ (tBDA.points 0) (tBDA.points 1) (tBDA.points 2) = π / 2)
    (hpHA0 : tHEA.points 0 = tHFA.points 0)
    (hpHA2 : tHEA.points 2 = tHFA.points 2)
    (hpDA1 : tCDA.points 1 = tBDA.points 1)
    (hpDA2 : tCDA.points 2 = tBDA.points 2)
    (h5 : ∠ (tHFB.points 0) (tHFB.points 1) (tHFB.points 2) = π / 2)
    (h6 : ∠ (tAEB.points 0) (tAEB.points 1) (tAEB.points 2) = π / 2)
    (h7 : ∠ (tHDB.points 0) (tHDB.points 1) (tHDB.points 2) = π / 2)
    (h8 : ∠ (tCEB.points 0) (tCEB.points 1) (tCEB.points 2) = π / 2)

    (hpHB0 : tHFB.points 0 = tHDB.points 0)
    (hpHB2 : tHFB.points 2 = tHDB.points 2)
    (hpEB1 : tAEB.points 1 = tCEB.points 1)
    (hpEB2 : tAEB.points 2 = tCEB.points 2)
    (h9 : ∠ (tHEC.points 0) (tHEC.points 1) (tHEC.points 2) = π / 2)
    (h10 : ∠ (tAFC.points 0) (tAFC.points 1) (tAFC.points 2) = π / 2)
    (h11 : ∠ (tHDC.points 0) (tHDC.points 1) (tHDC.points 2) = π / 2)
    (h12 : ∠ (tBFC.points 0) (tBFC.points 1) (tBFC.points 2) = π / 2)
    (hpHC0 : tHEC.points 0 = tHDC.points 0)
    (hpHC2 : tHEC.points 2 = tHDC.points 2)
    (hpFC1 : tAFC.points 1 = tBFC.points 1)
    (hpFC2 : tAFC.points 2 = tBFC.points 2)

    (h13 : ∠ (tHEA.points 1) (tHEA.points 2) (tHEA.points 0) = ∠ (tCDA.points 1) (tCDA.points 2) (tCDA.points 0))
    (h14 : ∠ (tHFA.points 1) (tHFA.points 2) (tHFA.points 0) = ∠ (tBDA.points 1) (tBDA.points 2) (tBDA.points 0))

    (h15 : ∠ (tHFB.points 1) (tHFB.points 2) (tHFB.points 0) = ∠ (tAEB.points 1) (tAEB.points 2) (tAEB.points 0))
    (h16 : ∠ (tHDB.points 1) (tHDB.points 2) (tHDB.points 0) = ∠ (tCEB.points 1) (tCEB.points 2) (tCEB.points 0))

    (h17 : ∠ (tHEC.points 1) (tHEC.points 2) (tHEC.points 0) = ∠ (tAFC.points 1) (tAFC.points 2) (tAFC.points 0))
    (h18 : ∠ (tHDC.points 1) (tHDC.points 2) (tHDC.points 0) = ∠ (tBFC.points 1) (tBFC.points 2) (tBFC.points 0))


    (hpEAC :  tHEC.points 1 =  tHEA.points 1)
    (hpTEC :  tHEC.points 2 = tABC.points 2 )
    (hpTEA :  tHEA.points 2 = tABC.points 0 )

    (hpTCDA_0 :  tCDA.points 0 = tABC.points 2)
    (hpTCDA_2 :  tCDA.points 2 = tABC.points 0)

    (hpTAFC_0 :  tAFC.points 0 = tABC.points 0)
    (hpTAFC_2 :  tAFC.points 2 = tABC.points 2)

    (hEInAC : dist (tHEA.points 1) (tABC.points 0) + dist (tHEA.points 1) (tABC.points 2) = dist (tABC.points 2) (tABC.points 0)) -- because E ∈ AC

    (hpFAB :  tHFB.points 1 =  tHFA.points 1)
    (hpTFA :  tHFA.points 2 = tABC.points 0 )
    (hpTFB :  tHFB.points 2 = tABC.points 1 )

    (hpTAEB_0 :  tAEB.points 0 = tABC.points 0)
    (hpTAEB_2 :  tAEB.points 2 = tABC.points 1)


    (hpTBDA_0 :  tBDA.points 0 = tABC.points 1)
    (hpTBDA_2 :  tBDA.points 2 = tABC.points 0)


    (hFInAB : dist (tHFA.points 1) (tABC.points 0) + dist (tHFA.points 1) (tABC.points 1) = dist (tABC.points 0) (tABC.points 1)) -- because F ∈ AB

    (hpDBC :  tHDB.points 1 =  tHDC.points 1)
    (hpTDB :  tHDB.points 2 = tABC.points 1 )
    (hpTDC :  tHDC.points 2 = tABC.points 2 )

    (hpTCEB_0 :  tCEB.points 0 = tABC.points 2)
    (hpTCEB_2 :  tCEB.points 2 = tABC.points 1)


    (hpTBFC_0 :  tBFC.points 0 = tABC.points 1)
    (hpTBFC_2 :  tBFC.points 2 = tABC.points 2)

    (hDInBC : dist (tHDB.points 1) (tABC.points 1) + dist (tHDB.points 1) (tABC.points 2) = dist (tABC.points 1) (tABC.points 2)) -- because D ∈ BC


    :
    dist (tABC.points 0) ( tABC.points 1) * dist (tABC.points 1) ( tABC.points 2) +
    dist (tABC.points 1) ( tABC.points 2) * dist (tABC.points 2) ( tABC.points 0) +
    dist (tABC.points 2) ( tABC.points 0) * dist (tABC.points 0) ( tABC.points 1)
    <= 2*(
    dist (tHEA.points 2) ( tHEA.points 0) * dist (tCDA.points 1) ( tCDA.points 2) +
    dist (tHFB.points 2) ( tHFB.points 0) * dist (tAEB.points 1) ( tAEB.points 2) +
    dist (tHEC.points 2) ( tHEC.points 0) * dist (tAFC.points 1) ( tAFC.points 2)
       )
    := by
    have hs1 := (two_triangles_simil tHEA tCDA h1 h2 h13).symm
    have hs2 := (two_triangles_simil tHFA tBDA h3 h4 h14).symm
    nth_rewrite 1 [← hpHA0] at hs2
    nth_rewrite 1 [← hpHA2] at hs2
    nth_rewrite 1 [← hpDA1] at hs2
    nth_rewrite 1 [← hpDA2] at hs2

    have hs3 := (two_triangles_simil tHFB tAEB h5 h6 h15).symm
    have hs4 := (two_triangles_simil tHDB tCEB h7 h8 h16).symm
    nth_rewrite 1 [← hpHB0] at hs4
    nth_rewrite 1 [← hpHB2] at hs4
    nth_rewrite 1 [← hpEB1] at hs4
    nth_rewrite 1 [← hpEB2] at hs4
    nth_rewrite 2 [mul_comm] at hs4

    have hs5 := (two_triangles_simil tHEC tAFC h9 h10 h17).symm
    have hs6 := (two_triangles_simil tHDC tBFC h11 h12 h18).symm
    nth_rewrite 1 [← hpHC0] at hs6
    nth_rewrite 1 [← hpHC2] at hs6
    nth_rewrite 1 [← hpFC1] at hs6
    nth_rewrite 1 [← hpFC2] at hs6
    have hmr :=
       calc  (2 ) * (
       dist (tHEA.points 2) ( tHEA.points 0) * dist (tCDA.points 1) ( tCDA.points 2) +
       dist (tHFB.points 2) ( tHFB.points 0) * dist (tAEB.points 1) ( tAEB.points 2) +
       dist (tHEC.points 2) ( tHEC.points 0) * dist (tAFC.points 1) ( tAFC.points 2)
       ) =
       (dist (tHEA.points 2) (tHEA.points 0) * dist (tCDA.points 1) (tCDA.points 2)) +
       (dist (tHEA.points 2) (tHEA.points 0) * dist (tCDA.points 1) (tCDA.points 2)) +
       (dist (tHFB.points 2) ( tHFB.points 0) * dist (tAEB.points 1) ( tAEB.points 2)) +
       (dist (tHFB.points 2) ( tHFB.points 0) * dist (tAEB.points 1) ( tAEB.points 2)) +
       (dist (tHEC.points 2) ( tHEC.points 0) * dist (tAFC.points 1) ( tAFC.points 2)) +
       (dist (tHEC.points 2) ( tHEC.points 0) * dist (tAFC.points 1) ( tAFC.points 2)) := by ring
       _ =  dist (tHEA.points 1) (tHEA.points 2) * dist (tCDA.points 2) (tCDA.points 0) +
            dist (tHFA.points 1) (tHFA.points 2) * dist (tBDA.points 2) (tBDA.points 0) +
            dist (tHFB.points 1) (tHFB.points 2) * dist (tAEB.points 2) (tAEB.points 0) +
            dist (tCEB.points 2) (tCEB.points 0) * dist (tHDB.points 1) (tHDB.points 2) +
            dist (tHEC.points 1) (tHEC.points 2) * dist (tAFC.points 2) (tAFC.points 0) +
            dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0) :=
               by nth_rewrite 1 [hs1] ; nth_rewrite 1 [hs2] ; nth_rewrite 1 [hs3] ; nth_rewrite 1 [hs4] ; nth_rewrite 1 [hs5] ; nth_rewrite 1 [hs6] ; ring
       _ =
           (dist (tHEA.points 1) (tHEA.points 2) * dist (tCDA.points 2) (tCDA.points 0)  +
            dist (tHEC.points 1) (tHEC.points 2) * dist (tAFC.points 2) (tAFC.points 0)) +

           (dist (tHFA.points 1) (tHFA.points 2) * dist (tBDA.points 2) (tBDA.points 0)  +
            dist (tHFB.points 1) (tHFB.points 2) * dist (tAEB.points 2) (tAEB.points 0)) +

           (dist (tHDB.points 1) (tHDB.points 2) * dist (tCEB.points 2) (tCEB.points 0)   +
            dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0)
           ) := by ring
       _ =
            (dist (tHEA.points 1) (tABC.points 0) + dist (tHEA.points 1) (tABC.points 2) ) * dist (tABC.points 2) (tABC.points 0)  +

           (dist (tHFA.points 1) (tHFA.points 2) * dist (tBDA.points 2) (tBDA.points 0)  +
            dist (tHFB.points 1) (tHFB.points 2) * dist (tAEB.points 2) (tAEB.points 0)) +

           (dist (tHDB.points 1) (tHDB.points 2) * dist (tCEB.points 2) (tCEB.points 0)   +
            dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0)) :=
              by rw [hpEAC] ; rw [hpTEC]
                 rw [hpTEA] ; rw [hpTCDA_0 ]
                 rw [hpTCDA_2 ] ; rw [hpTAFC_0 ] ; rw [hpTAFC_2 ] ;  nth_rewrite 2 [dist_comm] ; ring
       _ =  dist (tABC.points 2) (tABC.points 0) * dist (tABC.points 2) (tABC.points 0)  +

           (dist (tHFA.points 1) (tHFA.points 2) * dist (tBDA.points 2) (tBDA.points 0)  +
            dist (tHFB.points 1) (tHFB.points 2) * dist (tAEB.points 2) (tAEB.points 0)) +

           (dist (tHDB.points 1) (tHDB.points 2) * dist (tCEB.points 2) (tCEB.points 0)   +
            dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0)) := by rw [hEInAC ]

       _ =  dist (tABC.points 2) (tABC.points 0) * dist (tABC.points 2) (tABC.points 0)  +

            (dist (tHFA.points 1) (tABC.points 0)  + dist (tHFA.points 1) (tABC.points 1)) * dist (tABC.points 0) (tABC.points 1)    +

            (dist (tHDB.points 1) (tHDB.points 2) * dist (tCEB.points 2) (tCEB.points 0)   +
             dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0)) :=
               by rw [hpFAB , hpTFA , hpTFB , hpTBDA_0 , hpTBDA_2 , hpTAEB_0 , hpTAEB_2]
                  nth_rewrite 6 [dist_comm] ; ring

       _ =  dist (tABC.points 2) (tABC.points 0) * dist (tABC.points 2) (tABC.points 0)  +

            dist (tABC.points 0)   (tABC.points 1) * dist (tABC.points 0) (tABC.points 1)    +

            (dist (tHDB.points 1) (tHDB.points 2) * dist (tCEB.points 2) (tCEB.points 0)   +
             dist (tHDC.points 1) (tHDC.points 2) * dist (tBFC.points 2) (tBFC.points 0)) := by rw [hFInAB]

       _ =  dist (tABC.points 2) (tABC.points 0) * dist (tABC.points 2) (tABC.points 0)  +

            dist (tABC.points 0)   (tABC.points 1) * dist (tABC.points 0) (tABC.points 1)    +

            (dist (tHDB.points 1) (tABC.points 1) + dist (tHDB.points 1) (tABC.points 2)) * dist (tABC.points 1) (tABC.points 2) :=
               by  rw [hpDBC , hpTDB,  hpTDC ] ;
                   rw [hpTBFC_0, hpTBFC_2] ; rw [hpTCEB_0 , hpTCEB_2]
                   nth_rewrite 8 [dist_comm] ; ring
       _ =
            dist (tABC.points 0)   (tABC.points 1) * dist (tABC.points 0) (tABC.points 1)    +
            dist  (tABC.points 1)  (tABC.points 2) * dist (tABC.points 1) (tABC.points 2) +
            dist (tABC.points 2) (tABC.points 0) * dist (tABC.points 2) (tABC.points 0)  := by rw [hDInBC ] ; ring

    rw [hmr]
    apply ineq_3_nr (dist (tABC.points 0) (tABC.points 1))
         (dist (tABC.points 1) (tABC.points 2)) (dist (tABC.points 2) (tABC.points 0))
