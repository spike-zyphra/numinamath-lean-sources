import Mathlib
theorem algebra_605419 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x ^ 3 = z / y - 2 * y / z) (h2 : y ^ 3 = x / z - 2 * z / x)
    (h3 : z ^ 3 = y / x - 2 * x / y) :
    (x, y, z) = (1, 1, -1) ∨ (x, y, z) = (1, -1, 1) ∨ (x, y, z) = (-1, 1, 1) ∨ (x, y, z) = (-1, -1, -1) := by

  have eq1 : x ^ 3 * (y * z) = z ^ 2 - 2 * y ^ 2 := by
    have h1' : x ^ 3 = z / y - 2 * y / z := h1
    field_simp [hy, hz] at h1' ⊢
    nlinarith

  have eq2 : y ^ 3 * (x * z) = x ^ 2 - 2 * z ^ 2 := by
    have h2' : y ^ 3 = x / z - 2 * z / x := h2
    field_simp [hz, hx] at h2' ⊢
    nlinarith

  have eq3 : z ^ 3 * (x * y) = y ^ 2 - 2 * x ^ 2 := by
    have h3' : z ^ 3 = y / x - 2 * x / y := h3
    field_simp [hx, hy] at h3' ⊢
    nlinarith

  have h4 : x * y * z = -1 := by
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz, sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2)]

  have eq4 : 2 * y ^ 2 = x ^ 2 + z ^ 2 := by
    have eq1' : x ^ 3 * (y * z) = z ^ 2 - 2 * y ^ 2 := eq1
    have h4' : x * y * z = -1 := h4
    have h5 : x ^ 3 * (y * z) = x ^ 2 * (x * y * z) := by ring
    rw [h5] at eq1'
    rw [h4'] at eq1'
    nlinarith

  have eq5 : 2 * z ^ 2 = x ^ 2 + y ^ 2 := by
    have eq2' : y ^ 3 * (x * z) = x ^ 2 - 2 * z ^ 2 := eq2
    have h4' : x * y * z = -1 := h4
    have h5 : y ^ 3 * (x * z) = y ^ 2 * (x * y * z) := by ring
    rw [h5] at eq2'
    rw [h4'] at eq2'
    nlinarith

  have eq6 : 2 * x ^ 2 = y ^ 2 + z ^ 2 := by
    have eq3' : z ^ 3 * (x * y) = y ^ 2 - 2 * x ^ 2 := eq3
    have h4' : x * y * z = -1 := h4
    have h5 : z ^ 3 * (x * y) = z ^ 2 * (x * y * z) := by ring
    rw [h5] at eq3'
    rw [h4'] at eq3'
    nlinarith

  have eq7 : y ^ 2 = z ^ 2 := by
    nlinarith

  have eq8 : x ^ 2 = y ^ 2 := by
    nlinarith [eq7, eq5, eq6]

  have h13 : (x - y) * (x + y) = 0 := by
    have h10 : x ^ 2 = y ^ 2 := eq8
    nlinarith

  have h14 : (y - z) * (y + z) = 0 := by
    have h11 : y ^ 2 = z ^ 2 := eq7
    nlinarith

  cases (mul_eq_zero.mp h13) with
  | inl h15 =>
    have h150 : x = y := by linarith
    cases (mul_eq_zero.mp h14) with
    | inl h16 =>
      have h170 : y = z := by linarith
      have h180 : x = z := by
        linarith [h150, h170]
      have h190 : x ^ 3 = -1 := by
        have h200 : x * y * z = -1 := h4
        rw [show y = x by linarith [h150], show z = x by linarith [h180]] at h200
        nlinarith
      have h210 : x = -1 := by
        have h211 : x ^ 3 + 1 = 0 := by linarith
        have h212 : (x + 1) * (x ^ 2 - x + 1) = 0 := by
          ring_nf at h211 ⊢
          nlinarith
        cases (mul_eq_zero.mp h212) with
        | inl h213 =>
          linarith
        | inr h214 =>
          have h215 : x ^ 2 - x + 1 > 0 := by
            nlinarith [sq_nonneg (x - 1 / 2)]
          linarith
      have h220 : y = -1 := by
        linarith [h150, h210]
      have h230 : z = -1 := by
        linarith [h180, h210]
      simp [h210, h220, h230]
    | inr h16 =>
      have h171 : y = -z := by linarith
      have h181 : x = -z := by
        linarith [h150, h171]
      have h191 : x ^ 3 = 1 := by
        have h201 : x * y * z = -1 := h4
        rw [show y = x by linarith [h150], show z = -x by
          have h23 : z = -x := by
            linarith [h181]
          linarith [h23]
        ] at h201
        nlinarith
      have h211 : x = 1 := by
        have h212 : x ^ 3 - 1 = 0 := by linarith
        have h213 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
          ring_nf at h212 ⊢
          nlinarith
        cases (mul_eq_zero.mp h213) with
        | inl h214 =>
          linarith
        | inr h215 =>
          have h216 : x ^ 2 + x + 1 > 0 := by
            nlinarith [sq_nonneg (x + 1 / 2)]
          linarith
      have h221 : y = 1 := by
        linarith [h150, h211]
      have h231 : z = -1 := by
        linarith [h181, h211]
      simp [h211, h221, h231]
  | inr h15 =>
    have h151 : x = -y := by linarith
    cases (mul_eq_zero.mp h14) with
    | inl h16 =>
      have h172 : y = z := by linarith
      have h182 : x = -z := by
        linarith [h151, h172]
      have h192 : y ^ 3 = 1 := by
        have h202 : x * y * z = -1 := h4
        rw [show x = -y by linarith [h151], show z = y by linarith [h172]] at h202
        nlinarith
      have h212 : y = 1 := by
        have h213 : y ^ 3 - 1 = 0 := by linarith
        have h214 : (y - 1) * (y ^ 2 + y + 1) = 0 := by
          ring_nf at h213 ⊢
          nlinarith
        cases (mul_eq_zero.mp h214) with
        | inl h215 =>
          linarith
        | inr h216 =>
          have h217 : y ^ 2 + y + 1 > 0 := by
            nlinarith [sq_nonneg (y + 1 / 2)]
          linarith
      have h222 : x = -1 := by
        linarith [h151, h212]
      have h232 : z = 1 := by
        linarith [h172, h212]
      simp [h222, h232, h212]
    | inr h16 =>
      have h173 : y = -z := by linarith
      have h183 : x = z := by
        linarith [h151, h173]
      have h193 : z ^ 3 = 1 := by
        have h203 : x * y * z = -1 := h4
        rw [show x = z by linarith [h183], show y = -z by linarith [h173]] at h203
        nlinarith
      have h213 : z = 1 := by
        have h214 : z ^ 3 - 1 = 0 := by linarith
        have h215 : (z - 1) * (z ^ 2 + z + 1) = 0 := by
          ring_nf at h214 ⊢
          nlinarith
        cases (mul_eq_zero.mp h215) with
        | inl h216 =>
          linarith
        | inr h217 =>
          have h218 : z ^ 2 + z + 1 > 0 := by
            nlinarith [sq_nonneg (z + 1 / 2)]
          linarith
      have h223 : x = 1 := by
        linarith [h183, h213]
      have h233 : y = -1 := by
        linarith [h173, h213]
      simp [h223, h233, h213]