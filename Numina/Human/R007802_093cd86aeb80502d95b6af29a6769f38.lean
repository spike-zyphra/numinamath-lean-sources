import Mathlib

open Polynomial

/- Real numbers r and s are roots of p(x)=x^3+ax+b, and r+4 and s−3 are roots of q(x)=x^3+ax+b+240. Find the sum of all possible values of ∣b∣. -/
theorem algebra_96084 :
    ∑ᶠ b ∈ {b : ℝ | ∃ a r s t u, (X ^ 3 + C a * X + C b).roots = {r, s, t} ∧ (X ^ 3 + C a * X + C (b + 240)).roots = {r + 4, s - 3, u}}, |b| = 420 := by
  -- it is enough to show that all possible values of b are b = -330 or b = 90
  suffices h : {b : ℝ | ∃ a r s t u, (X ^ 3 + C a * X + C b).roots = {r, s, t} ∧ (X ^ 3 + C a * X + C (b + 240)).roots = {r + 4, s - 3, u}} = {-330, 90} by
    rw [h, finsum_mem_eq_toFinset_sum]
    norm_num
  ext b
  simp only [map_add, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  symm
  constructor
  -- First, show that if b = -330 or b = 90 then there exist a, r, s, t, u such that
  -- X^3 + a * X + b has roots {r, s, t} and X^3 + a * X + (b + 240) has roots {r + 4, s - 3, u}
  · intro h
    cases' h with h h
    -- if b = -330 then take a = 30 - 11 ^ 2, r = -5, s = -6, t = 11, u = 10
    -- and demonstrate that all coniditions are satisfied
    · use 30 - 11 ^ 2, -5, -6, 11, 10
      have eq1 : X ^ 3 + C (30 - 11 ^ 2 : ℝ) * X + C (-330) = ∏ x ∈ {-5, -6, 11}, (X - C x) := by
        norm_num
        simp [map_ofNat]
        ring
      have eq2 : X ^ 3 + C (30 - 11 ^ 2 : ℝ) * X + (C (-330) + C 240) = ∏ x ∈ {-1, -9, 10}, (X - C x) := by
        norm_num
        simp [map_ofNat]
        ring
      simp_rw [h, eq1, eq2, roots_prod_X_sub_C]
      norm_num
    -- if b = 90 then take a = -91, r = 1, s = 9, t = -10, u = -11
    -- and demonstrate that all coniditions are satisfied
    · use -91, 1, 9, -10, -11
      have eq1 : X ^ 3 + C (-91 : ℝ) * X + C 90 = ∏ x ∈ {1, 9, -10}, (X - C x) := by
        norm_num
        simp [map_ofNat]
        ring
      have eq2 : X ^ 3 + C (-91 : ℝ) * X + (C 90 + C 240) = ∏ x ∈ {5, 6, -11}, (X - C x) := by
        norm_num
        simp [map_ofNat]
        ring
      simp_rw [h, eq1, eq2, roots_prod_X_sub_C]
      norm_num
  -- now we need to show that if p := X ^ 3 + a * X + b has roots {r, s, t} and
  -- q := X ^ 3 + a * X + (b + 240) has roots {r + 4, s - 3, u} then b = -330 or b = 90
  · intro ⟨a, r, s, t, u, hr1, hr2⟩
    rw [←map_add] at hr2
    set p : Polynomial ℝ := X ^ 3 + _ + C b
    set q : Polynomial ℝ := X ^ 3 + _ + _
    -- use Vieta's identities to derive equations between coefficients of a cubic polynomial
    -- and its roots
    have h {a b r s t : ℝ} (hr : (X ^ 3 + C a * X + C b).roots = {r, s, t}) :
        0 = -(r + s + t) ∧ a = r * s + r * t + s * t ∧ b = -(r * s * t) := by
      let p3 : Cubic ℝ := { a := 1, b := 0, c := a, d := b }
      have p3_eq : p3.toPoly = X ^ 3 + C a * X + C b := by simp [Cubic.toPoly]
      have hroots : (Cubic.map (RingHom.id ℝ) p3).roots = {r, s, t} := by simp [Cubic.map_roots, p3_eq, hr]
      have := Cubic.eq_sum_three_roots (by norm_num) hroots
      simp [Cubic.map] at this
      simp [this]
    -- we derive the following equalities:
    -- eq1: 0 = -(r + s + t)
    -- eq2: a = r * s + r * t + s * t
    -- eq3: b = -(r * s * t)
    -- eq4: 0 = -(r + 4 + s - 3 + u)
    -- eq5: a = (r + 4) * (s - 3) + (r + 4) * u + (s - 3) * u
    -- eq6: b + 240 = -(r + 4) * (s - 3) * u
    have ⟨eq1, eq2, eq3⟩ := h hr1
    have ⟨eq4, eq5, eq6⟩ := h hr2
    clear * - eq1 eq2 eq3 eq4 eq5 eq6
    -- it is easy to derive that t = -r - s and u = -r - s - 1
    have ht : t = -r - s := by linarith
    have hu : u = -r - s - 1 := by linarith
    subst t u
    clear eq1 eq4
    -- from eq2 and eq5 we derive that s = (5 * r + 13) / 2
    have hs : s = (5 * r + 13) / 2 := by linarith
    rw [eq3, ←sub_eq_zero] at eq6
    subst s
    ring_nf at eq3 eq6
    clear eq5 eq2
    -- eq6 simplifies to -27 * (r - 1) * (r + 5) = 0
    have eq : -27 * (r - 1) * (r + 5) = 0 := by rw [←eq6]; ring
    simp_rw [mul_eq_zero] at eq
    -- so r = 1 or r = -5
    have hr : r = 1 ∨ r = -5 := by
      norm_num at eq
      cases eq <;> [left; right] <;> linarith
    -- r = 1 implies b = 90 and r = -5 implies b = -330
    cases hr <;> (subst r; norm_num at eq3; tauto)