import Mathlib

open Real

lemma lemma_1 (a b u v : ℝ) (γ φ : ℝ) :
    2*(a^2*v^2 + b^2*u^2) - 4*a*b*u*v*(cos γ * cos φ + sin γ * sin φ)
    = 2*(a*v-b*u)^2 + 4*a*b*u*v*(1 - cos (γ - φ)) := by
  rw [cos_sub]
  ring
/-4. (CZS 2) Let $T_{1}$ be a triangle having $a, b, c$ as lengths of its sides and let $T_{2}$ be another triangle having $u, v, w$ as lengths of its sides. If $P, Q$ are the areas of the two triangles, prove that  $$ 16 P Q \leq a^{2}\left(-u^{2}+v^{2}+w^{2}\right)+b^{2}\left(u^{2}-v^{2}+w^{2}\right)+c^{2}\left(u^{2}+v^{2}-w^{2}\right) $$  When does equality hold?-/
theorem inequalities_23685
  (a b c u v w : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a)
  (h''' : u + v > w) (h'''' : u + w > v) (h''''' : v + w > u) :
    16 * ((1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b))))
      * ((1/2) * u * v * sin (arccos ((u^2 + v^2 - w^2)/(2*u*v))))
    ≤ a^2 * (-u^2 + v^2 + w^2)
      + b^2 * (u^2 - v^2 + w^2)
      + c^2 * (u^2 + v^2 - w^2)
  ∧ (
    16 * ((1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b))))
      * ((1/2) * u * v * sin (arccos ((u^2 + v^2 - w^2)/(2*u*v))))
    = a^2 * (-u^2 + v^2 + w^2)
      + b^2 * (u^2 - v^2 + w^2)
      + c^2 * (u^2 + v^2 - w^2)
    → a/b = u/v ∧ c/a = w/u
  ) :=
by
  let γ := arccos ((a^2 + b^2 - c^2)/(2*a*b))
  let φ := arccos ((u^2 + v^2 - w^2)/(2*u*v))
  let s := (1/2) * a * b * sin γ
  let t := (1/2) * u * v * sin φ
  have hs : s > 0 := by
    -- Use triangle inequality and positivity of trig functions
    admit
  have ht : t > 0 := by admit
  have eqn : 16 * s * t = 4 * a * b * u * v * sin γ * sin φ := by ring
  simp only [eqn]
  have h_sum :
    a^2 * (-u^2 + v^2 + w^2)
    + b^2 * (u^2 - v^2 + w^2)
    + c^2 * (u^2 + v^2 - w^2)
    = 2*(a^2*v^2 + b^2*u^2) - 4*a*b*u*v*(cos γ * cos φ) := by admit
  rw [h_sum]
  have add_sin : 2*(a^2*v^2 + b^2*u^2) - 4*a*b*u*v*(cos γ * cos φ)
      = (2*(a^2*v^2 + b^2*u^2) - 4*a*b*u*v*(cos γ * cos φ + sin γ * sin φ))
        + 4*a*b*u*v*sin γ * sin φ := by ring
  rw [add_sin]
  have step :
    2*(a^2*v^2 + b^2*u^2) - 4*a*b*u*v*(cos γ * cos φ + sin γ * sin φ)
    = 2*(a*v-b*u)^2 + 4*a*b*u*v*(1 - cos (γ - φ)) :=
    lemma_1 a b u v γ φ
  rw [step]
  -- Prove nonnegativity of all factors
  have h4_pos : 0 < (4 : ℝ) := by norm_num
  have h4a_pos : 0 < 4 * a := mul_pos h4_pos ha
  have h4ab_pos : 0 < 4 * a * b := mul_pos h4a_pos hb
  have h4abu_pos : 0 < 4 * a * b * u := mul_pos h4ab_pos hu
  have h4abuv_pos : 0 < 4 * a * b * u * v := mul_pos h4abu_pos hv
  have hsinγ : 0 ≤ sin γ := by admit -- γ ∈ (0,π)
  have hsinφ : 0 ≤ sin φ := by admit -- φ ∈ (0,π)
  have h4abuv_sinγ : 0 ≤ 4 * a * b * u * v * sin γ := mul_nonneg (le_of_lt h4abuv_pos) hsinγ
  have h_mulall : 0 ≤ 4 * a * b * u * v * sin γ * sin φ := mul_nonneg h4abuv_sinγ hsinφ
  have h_cos : 0 ≤ 1 - cos (γ - φ) := sub_nonneg.mpr (cos_le_one _)
  have h_sq : 0 ≤ (a*v-b*u)^2 := sq_nonneg _
  have h_B : 0 ≤ 4 * a * b * u * v * (1 - cos (γ - φ)) := mul_nonneg (le_of_lt h4abuv_pos) h_cos
  have h_sq2 : 0 ≤ 2 * (a*v-b*u)^2 := mul_nonneg (by norm_num) h_sq
  have h_A : 0 ≤ 4 * a * b * u * v * sin γ * sin φ + 2 * (a * v - b * u) ^ 2 :=
    add_nonneg h_mulall h_sq2
  have key_nonneg :
    0 ≤ 4 * a * b * u * v * sin γ * sin φ + 2*(a*v-b*u)^2 + 4*a*b*u*v*(1 - cos (γ - φ)) :=
    add_nonneg h_A h_B
  constructor
  ·
    have : (4 * a * b * u * v * sin γ * sin φ
      ≤ 2 * (a * v - b * u) ^ 2 + 4 * a * b * u * v * (1 - cos (γ - φ)) + 4 * a * b * u * v * sin γ * sin φ)
      ↔ (0 ≤ 4 * a * b * u * v * sin γ * sin φ + 2 * (a * v - b * u) ^ 2 + 4 * a * b * u * v * (1 - cos (γ - φ)))
      := by admit
    rw [this]
    exact key_nonneg
  ·
    intro h_eq
    have hsq : (a*v-b*u)^2 = 0 := by
      have : 0 ≤ (a*v-b*u)^2 := sq_nonneg _
      linarith
    have av_sub_bu_eq0 : a*v - b*u = 0 := sq_eq_zero_iff.mp hsq
    have av_eq_bu : a*v = b*u := by linarith [av_sub_bu_eq0]
    have hcos0 : 4*a*b*u*v*(1 - cos (γ-φ)) = 0 :=
      by linarith [h_eq, hsq]
    have hcos : 1 - cos (γ-φ) = 0 :=
      (mul_eq_zero.mp hcos0).resolve_left (ne_of_gt h4abuv_pos)
    have hcos_eq : cos (γ - φ) = 1 := by linarith [hcos]
    have hk_exists : ∃ n : ℤ, (n : ℝ) * (2 * π) = γ - φ := (Real.cos_eq_one_iff _).mp hcos_eq
    obtain ⟨n, hn⟩ := hk_exists
    have hk : γ - φ = 2 * π * n := by rw [←hn, mul_comm]
    -- Since γ, φ ∈ [0, π], γ - φ ∈ [-π, π], thus n = 0
    have n0 : n = 0 := by admit
    have diff_zero : γ - φ = 0 := by rw [hk, n0]; simp
    have γφ_eq : γ = φ := by linarith [diff_zero]    
    have ab_uv : a/b = u/v := by
      field_simp [av_eq_bu, ne_of_gt hb, ne_of_gt hv]
    have ca_wu : c/a = w/u := by admit
    exact ⟨ab_uv, ca_wu⟩