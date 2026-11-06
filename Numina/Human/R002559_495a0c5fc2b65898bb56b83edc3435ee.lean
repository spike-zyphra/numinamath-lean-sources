import Mathlib
open Real

/-
Let $ABCD$ be a tetrahedron with $AB=41$, $AC=7$, $AD=18$, $BC=36$, $BD=27$, and $CD=13$, as shown in the figure. Let $d$ be the distance between the midpoints of edges $AB$ and $CD$. Find $d^{2}$.
-/

theorem geometry_95433
  (A B C D : EuclideanSpace ℝ (Fin 3))
  (h₀ : dist A B = 41)
  (h₁ : dist A C = 7)
  (h₂ : dist A D = 18)
  (h₃ : dist B C = 36)
  (h₄ : dist B D = 27)
  (h₅ : dist C D = 13)
  : dist ( midpoint ℝ A B ) ( midpoint ℝ C D ) ^ 2 = 137
:= by
  set M := midpoint ℝ A B with hM
  set N := midpoint ℝ C D with hN
  -- We first derive the median formula, which is well-known
  have median : ∀ (X Y Z : EuclideanSpace ℝ (Fin 3)), dist X (midpoint ℝ Y Z) = √((2 * (dist X Y)^2 + 2 * (dist X Z)^2 - (dist Y Z)^2) / 4) := by
    -- This is an immediate consequence of the parallelogram law
    intro X Y Z
    repeat rw [dist_eq_norm]
    set x := X - Y with hx
    set y := X - Z with hy
    have : y - x = Y - Z := by
      rw [hx, hy]
      field_simp
    rw [← this]
    have : ‖X - (midpoint ℝ Y Z)‖ = ‖(x + y)‖ / 2 := by
      rw [midpoint_eq_smul_add, hx, hy]
      field_simp
      rw [mul_comm, (by norm_num : 2 = ‖(2 : ℝ)‖), ← norm_smul, smul_sub, smul_add]
      simp_rw [← smul_assoc, (by norm_num : (2 : ℝ) • (1 / ‖(2 : ℝ)‖) = 1), one_smul]
      have : X - Y + (X - Z) = (2 : ℝ) • X - (Y + Z) := by
        rw [two_smul, add_sub, sub_add_eq_add_sub, sub_sub]
      rw [this]
    rw [this, (by norm_num : (4 : ℝ) = 2 * 2)]; symm
    rw [Real.sqrt_eq_iff_eq_sq]
    have : ‖x + y‖^2 + ‖x - y‖^2 = 2 * (‖x‖^2 + ‖y‖^2) := by
      simp_rw [← real_inner_self_eq_norm_sq]
      exact parallelogram_law
    rw [← mul_add, ← this]
    nth_rw 2 [norm_sub_rev]
    ring
    . rw [(by norm_num : (0 : ℝ) = 0 / (2 * 2)), div_le_div_iff_of_pos_right (by norm_num)]
      calc
        0 ≤ (‖y‖ - ‖x‖)^2 := by
          exact sq_nonneg (‖y‖ - ‖x‖)
        _ = 2 * ‖x‖^2 + 2 * ‖y‖^2 - (‖y‖ + ‖x‖)^2 := by
          ring
        _ ≤ 2 * ‖x‖^2 + 2 * ‖y‖^2 - ‖y - x‖^2 := by
          have : ‖y - x‖^2 ≤ (‖y‖ + ‖x‖)^2 := by
            rw [sq_le_sq]
            have : |‖y‖ + ‖x‖| = ‖y‖ + ‖x‖ := by
              apply abs_of_nonneg
              linarith [norm_nonneg x, norm_nonneg y]
            simpa [this] using norm_sub_le y x
          linarith
    . linarith [norm_nonneg (x + y)]

  -- We then apply the formula three times, on `▵CAB`, `▵DAB` and `▵MCD`, repectively

  -- We can find `CM`
  have l_CM : dist C M = √(1009 / 4) := by
    have := median C A B
    have h₁ : dist C A = 7 := by simpa [dist_comm] using h₁
    have h₃ : dist C B = 36 := by simpa [dist_comm] using h₃
    conv at this =>
      rw [← hM, h₁, h₃, h₀]
      norm_num
    simpa

  -- We can find `DM`
  have l_DM : dist D M = √(425 / 4) := by
    have := median D A B
    have h₂ : dist D A = 18 := by simpa [dist_comm] using h₂
    have h₄ : dist D B = 27 := by simpa [dist_comm] using h₄
    conv at this =>
      rw [← hM, h₂, h₄, h₀]
      norm_num
    simpa

  -- And finally `MN`
  have l_MN : dist M N = √137 := by
    have := median M C D
    have l_MC : dist M C = √(1009 / 4) := by simpa [dist_comm] using l_CM
    have l_MD : dist M D = √(425 / 4) := by simpa [dist_comm] using l_DM
    conv at this =>
      rw [← hN, l_MC, l_MD, h₅]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1009 / 4)]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 425 / 4)]
      norm_num
    simpa

  -- The rest is algebra
  rw [l_MN]
  simpa