import Mathlib

/-Let $A, B, C$ be points in that order along a line, such that $A B=20$ and $B C=18$. Let $\omega$ be a circle of nonzero radius centered at $B$, and let $\ell_{1}$ and $\ell_{2}$ be tangents to $\omega$ through $A$ and $C$, respectively. Let $K$ be the intersection of $\ell_{1}$ and $\ell_{2}$. Let $X$ lie on segment $\overline{K A}$ and $Y$ lie on segment $\overline{K C}$ such that $X Y \| B C$ and $X Y$ is tangent to $\omega$. What is the largest possible integer length for $X Y$ ?
-/

open Real

theorem geometry_609931 :
    ∀ (KA KC KX KY XY AC : ℝ) (x : ℝ),
    -- These lengths must be positive.
    (KA > 0 ∧ KC > 0 ∧ KX > 0 ∧ KY > 0 ∧ AC > 0 ∧ x > 1) →
    (AC = 38) →
    (KA = KX + 20) → -- From AX = 20
    (KC = KY + 18) → -- From YC = 18
    (KX / KA = KY / KC) → -- From similarity △KXY ~ △KAC
    (KA < KC + AC) → -- From triangle inequality on △KAC
    (XY / AC = KX / KA) → -- From similarity
    XY < 36 := by

  intro KA KC KX KY XY AC x h_pos h_ac h_ka h_kc h_sim1 h_tri_ineq h_sim2

  -- From the similarity ratio `KX/KA = KY/KC` and the segment additions,
  -- we can establish a relationship between KA and KC.
  have h_KA_KC_ratio : KA / KC = 20 / 18 := by
    rw [h_ka, h_kc] at h_sim1
    have h1 : KX * (KY + 18) = KY * (KX + 20) := by
      apply (div_eq_div_iff (by linarith) (by linarith)).mp h_sim1
    have h2 : 18 * KX = 20 * KY := by linarith [h1]

    have h_ky_subst : KY = (18 / 20) * KX := by field_simp [h2]
    rw [h_kc, h_ky_subst]
    have : (18 * KX + 18 * 20) ≠ 0 := by linarith
    field_simp
    rw[h_ka]
    ring

  -- Let's use the parameterization `KA = 20x` and `KC = 18x`.
  -- This is consistent with the ratio we just proved.
  have h_param : ∃ x' > 1, KA = 20 * x' ∧ KC = 18 * x' := by
    -- From `KA/KC = 20/18`, we know `18*KA = 20*KC`.
    have h_cross_mul : 18 * KA = 20 * KC := by
      rw [div_eq_div_iff] at h_KA_KC_ratio
      · rw [mul_comm] at h_KA_KC_ratio; exact h_KA_KC_ratio
      · linarith [h_pos.2.1]
      · norm_num
    -- Let `x = KA / 20`. Then `KA = 20x`.
    use KA / 20
    constructor
    · linarith
    · constructor
      · field_simp
      · have : 20 * KC = 18 * KA := h_cross_mul.symm
        field_simp; linarith

  -- We can now work with the parameter `x`.
  rcases h_param with ⟨x, hx_gt_1, h_ka_x, h_kc_x⟩
  
  -- Apply the triangle inequality to find a bound on `x`.
  rw [h_ka_x, h_kc_x, h_ac] at h_tri_ineq
  have hx_lt_19 : x < 19 := by linarith

  -- Now use the second similarity ratio to find XY in terms of `x`.

  have h_kx_x : KX = 20 * (x - 1) := by
    rw [h_ka] at h_ka_x; linarith
  
  have h_xy_x : XY = 38 * (x - 1) / x := by

    rw [h_ac, h_ka_x, h_kx_x] at h_sim2

    have h_rhs_simplified : (20 * (x - 1)) / (20 * x) = (x - 1) / x := by
      have hx_ne_zero : x ≠ 0 := by linarith [hx_gt_1]
      field_simp [hx_ne_zero]
      ring
    rw [h_rhs_simplified] at h_sim2

    rw [div_eq_iff (by norm_num)] at h_sim2
    rw [mul_comm] at h_sim2
    rw [h_sim2]
    ring_nf
  
  rw [h_xy_x]
  rw [div_lt_iff₀ (by linarith [hx_gt_1])]
  linarith


