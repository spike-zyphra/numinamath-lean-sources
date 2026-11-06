import Mathlib

theorem algebra_231755 :
    {(d, t) : ℝ × ℝ | ∃ vA vB : ℝ, d > 0 ∧ vA > 0 ∧ vB > 0 ∧ vA > vB ∧
    (d + 100) / vA = (d - 100) / vB ∧
    2 * d / vA + 4 = 2 * d / vB ∧
    (2 * d + d/5) / vA = (2 * d - d/5) / vB ∧
    t = 2 * d / vA} = {(1000, 18)} := by
  ext ⟨d, t⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if $(d, t)$ satisfies all conditions, then $(d, t) = (1000, 18)$.
    rintro ⟨vA, vB, h1, h2, h3, h4, h5, h6, h7, h8⟩
    have eq1 : (d + 100) * vB = (d - 100) * vA := by
      have h5' : (d + 100) / vA = (d - 100) / vB := by linarith
      have h5'' : vA ≠ 0 := by linarith
      have h5''' : vB ≠ 0 := by linarith
      field_simp at h5'
      nlinarith
    have eq2 : 2 * d * vB + 4 * vA * vB = 2 * d * vA := by
      have h6' : 2 * d / vA + 4 = 2 * d / vB := by linarith
      have h5'' : vA ≠ 0 := by linarith
      have h5''' : vB ≠ 0 := by linarith
      field_simp at h6'
      nlinarith [mul_pos h2 h3]
    have eq3 : 11 * d * vB = 9 * d * vA := by
      have h7' : (2 * d + d/5) / vA = (2 * d - d/5) / vB := by linarith
      have h5'' : vA ≠ 0 := by linarith
      have h5''' : vB ≠ 0 := by linarith
      field_simp at h7'
      ring_nf at h7'
      nlinarith [mul_pos h2 h3]
    -- From eq3 we can simplify to get $11 \cdot vB = 9 \cdot vA$ by factoring with $d$.
    have eq4 : 11 * vB = 9 * vA := by
      have h15 : d > 0 := h1
      have h14 : d ≠ 0 := by linarith
      apply (mul_left_inj' (show d ≠ 0 by linarith)).mp
      nlinarith
    -- Now from eq4 $11 \cdot vB = 9 \cdot vA$ rewrite to get $vB = \frac{9}{11} \cdot vA$.
    have eq5 : vB = (9/11) * vA := by
      nlinarith
    -- Substitute `eq5` into eq1.
    -- From eq1 : (d + 100) * vB = (d - 100) * vA.
    -- Substituting $vB = \frac{9}{11} \cdot vA$ gives:
    -- $(d + 100) \cdot \frac{9}{11} \cdot vA = (d - 100) \cdot vA$.
    -- Since $vA > 0$, we can divide by $vA$.
    -- Get $\frac{9}{11}(d + 100) = d - 100$.
    -- Multiply both sides by 11 to get $9(d + 100) = 11(d - 100)$.
    -- Expanding: $9d + 900 = 11d - 1100$.
    -- Therefore, $2000 = 2d$, so $d = 1000$.
    have eq6 : d = 1000 := by
      have h32 : (d + 100) * vB = (d - 100) * vA := eq1
      rw [show vB = (9/11) * vA by linarith [eq5]] at h32
      have h34 : vA > 0 := h2
      have h34 : vA ≠ 0 := by linarith
      have h43 : vA * ((d + 100) * (9/11) - (d - 100)) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h43) with
      | inl h13 =>
        linarith
      | inr h14 =>
        nlinarith
    -- Substituting $d = 1000$ and $vB = \frac{9}{11} \cdot vA$ into `eq2`.
    -- `eq2 : 2 * d * vB + 4 * vA * vB = 2 * d * vA`.
    -- Substituting gets: $2000 \cdot \frac{9}{11} \cdot vA + 4 \cdot \frac{9}{11} \cdot vA^2 = 2000 \cdot vA$.
    -- Rearranged: $4 \cdot \frac{9}{11} \cdot vA^2 - 2000 \cdot vA + 18000/11 \cdot vA = 0$.
    -- So quadratic: $\frac{36}{11}vA^2 - \frac{22000}{11}vA = 0$ which factors to $ vA \cdot (36 vA - 22000) = 0 $.
    -- So either $vA = 0$ (contradicts with `h2 : vA > 0`) or $36 vA - 22000 = 0$, i.e., $36 vA = 22000$.
    -- Solving: `vA = 22000/36 = 6111.1111` which means `vA = 1000/9`.
    have eq7' : vA = (1000/9) := by
      rw [show d = 1000 by linarith [eq6]] at eq2
      rw [show vB = (9/11) * vA by linarith [eq5]] at eq2
      nlinarith [sq_pos_of_pos h2, sq_nonneg (vA - (1000/9)), mul_pos h2 h3]
    -- Now from h8 : t = 2 * d / vA.
    -- Substitute $d = 1000$, $vA = \frac{1000}{9}$ to get $t = \frac{2000}{\frac{1000}{9}} = 18$.
    have eq7 : t = 18 := by
      rw [h8]
      rw [eq7']
      rw [show d = 1000 by linarith [eq6]]
      norm_num
    -- Final equality.
    simp [eq6, eq7]
  · -- Second direction: if $(d, t) = (1000, 18)$, then all conditions are met.
    rintro ⟨rfl, rfl⟩
    use 1000 / 9, 1000 / 11
    constructor
    · norm_num -- d > 0
    constructor
    · norm_num -- vA > 0
    constructor
    · norm_num -- vB > 0
    constructor
    · norm_num -- vA > vB
    constructor
    · norm_num -- (d + 100) / vA = (d - 100) / vB
    constructor
    · norm_num -- 2 * d / vA + 4 = 2 * d / vB
    constructor
    · norm_num -- (2 * d + d/5) / vA = (2 * d - d/5) / vB
    · norm_num -- t = 2 * d / vA