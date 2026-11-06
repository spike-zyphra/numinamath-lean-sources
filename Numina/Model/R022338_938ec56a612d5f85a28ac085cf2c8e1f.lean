import Mathlib

theorem algebra_184978 (s t : ℝ) (a b c : ℝ) (h₀ : s ≠ 0) (h₁ : t ≠ 0)
    (h₂ : s * a^2 * (a - 1) + t * (a + 1) = 0) (h₃ : s * b^2 * (b - 1) + t * (b + 1) = 0)
    (h₄ : s * c^2 * (c - 1) + t * (c + 1) = 0) (h₅ : a ≠ b) (h₆ : a ≠ c) (h₇ : b ≠ c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) = -1 := by

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [show a = 0 by linarith] at h₂
    have ht : t = 0 := by
      nlinarith
    contradiction

  have hb1 : b ≠ 0 := by
    by_contra h
    rw [show b = 0 by linarith] at h₃
    have ht : t = 0 := by
      nlinarith
    contradiction

  have hc1 : c ≠ 0 := by
    by_contra h
    rw [show c = 0 by linarith] at h₄
    have ht : t = 0 := by
      nlinarith
    contradiction

  have eq1 : s * a^3 - s * a^2 + t * a + t = 0 := by
    have h : s * a^2 * (a - 1) + t * (a + 1) = 0 := h₂
    linarith [h]

  have eq2 : s * b^3 - s * b^2 + t * b + t = 0 := by
    have h : s * b^2 * (b - 1) + t * (b + 1) = 0 := h₃
    linarith [h]

  have eq3 : s * c^3 - s * c^2 + t * c + t = 0 := by
    have h : s * c^2 * (c - 1) + t * (c + 1) = 0 := h₄
    linarith [h]

  have eq4 : (a - b) * (s * (a^2 + a * b + b^2 - (a + b)) + t) = 0 := by
    have h8 : s * a^3 - s * a^2 + t * a + t - (s * b^3 - s * b^2 + t * b + t) = 0 := by
      linarith [eq1, eq2]
    have h9 : s * a^3 - s * a^2 + t * a + t - (s * b^3 - s * b^2 + t * b + t) =
        (a - b) * (s * (a^2 + a * b + b^2 - (a + b)) + t) := by
      ring
    rw [h9] at h8
    linarith

  have h10 : a - b ≠ 0 := by
    intro h11
    apply h₅
    linarith

  have eq5 : s * (a^2 + a * b + b^2 - (a + b)) + t = 0 := by
    apply (mul_left_inj' h10).mp
    linarith

  have eq6 : s * (b^2 + b * c + c^2 - (b + c)) + t = 0 := by
    have eq7 : (b - c) * (s * (b^2 + b * c + c^2 - (b + c)) + t) = 0 := by
      have h8 : s * b^3 - s * b^2 + t * b + t - (s * c^3 - s * c^2 + t * c + t) = 0 := by
        linarith [eq2, eq3]
      have h9 : s * b^3 - s * b^2 + t * b + t - (s * c^3 - s * c^2 + t * c + t) =
          (b - c) * (s * (b^2 + b * c + c^2 - (b + c)) + t) := by
        ring
      rw [h9] at h8
      linarith
    have h10 : b - c ≠ 0 := by
      intro h11
      apply h₇
      linarith
    have h11 : s * (b^2 + b * c + c^2 - (b + c)) + t = 0 := by
      apply (mul_left_inj' h10).mp
      linarith
    linarith

  have eq7 : s * (a^2 + a * b + b^2 - (a + b) - (b^2 + b * c + c^2 - (b + c)) ) = 0 := by
    nlinarith [eq5, eq6]

  have eq8 : (a - c) * (s * (a + b + c - 1)) = 0 := by
    ring_nf at eq7 ⊢
    linarith [eq7]

  have h10 : a - c ≠ 0 := by
    intro h11
    apply h₆
    linarith

  have eq9 : s * (a + b + c - 1) = 0 := by
    apply (mul_left_inj' h10).mp
    linarith

  have h8 : a + b + c - 1 = 0 := by
    apply (mul_left_inj' h₀).mp
    linarith

  have h9 : a + b + c = 1 := by linarith

  have h13 : s * (a * b + b * c + c * a) = t := by
    nlinarith [sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_pos_of_ne_zero (show a - b ≠ 0 by intro h11; apply h₅; linarith), sq_pos_of_ne_zero (show a - c ≠ 0 by intro h11; apply h₆; linarith), sq_pos_of_ne_zero (show b - c ≠ 0 by intro h11; apply h₇; linarith)]

  have h14 : s * (a * b * c) = -t := by
    nlinarith [sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_pos_of_ne_zero (show a - b ≠ 0 by intro h11; apply h₅; linarith), sq_pos_of_ne_zero (show a - c ≠ 0 by intro h11; apply h₆; linarith), sq_pos_of_ne_zero (show b - c ≠ 0 by intro h11; apply h₇; linarith)]

  have h15 : a * b + b * c + c * a = t / s := by
    have h100 : s ≠ 0 := h₀
    field_simp [h100]
    linarith [h13]

  have h16 : a * b * c = -t / s := by
    have h100 : s ≠ 0 := h₀
    field_simp [h100]
    linarith [h14]

  have h17 : (a + b + c) * (1 / a + 1 / b + 1 / c) = -1 := by
    have h100 : a + b + c = 1 := h9
    have h101 : a * b + b * c + c * a = t / s := h15
    have h102 : a * b * c = -t / s := h16
    have h103 : 1 / a + 1 / b + 1 / c = (a * b + b * c + c * a) / (a * b * c) := by
      field_simp [ha1, hb1, hc1]
      <;> ring
    rw [h103]
    rw [h101, h102]
    have h1000 : s ≠ 0 := h₀
    have h1001 : t ≠ 0 := h₁
    field_simp [h1000, h1001]
    <;> nlinarith

  exact h17