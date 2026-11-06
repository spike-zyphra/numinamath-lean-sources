import Mathlib


lemma lemma_1 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 := by
  have h1 : a + b + c ≠ 0 := by
    by_contra h2
    have h3 : a + b + c = 0 := by linarith
    have h4 : 1 / (a + b + c) = 0 := by
      rw [show a + b + c = 0 by linarith]
      norm_num
    have h5 : 1 / a + 1 / b + 1 / c = 0 := by linarith [h, h4]
    have h6 : a * b + a * c + b * c = 0 := by
      field_simp [ha, hb, hc] at h5 ⊢
      <;> nlinarith
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
      have h8 : a + b + c = 0 := by linarith
      have h9 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
        nlinarith
      rw [h8, h6] at h9
      nlinarith
    have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, h7]
    contradiction
  field_simp [ha, hb, hc, h1] at h
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c), sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (a * c - b * c)]


theorem algebra_198151 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    ∀ k : ℕ, Odd k → 1 / a ^ k + 1 / b ^ k + 1 / c ^ k = 1 / (a ^ k + b ^ k + c ^ k) := by
  intro k hk
  have h1 : a + b + c ≠ 0 := by
    by_contra h2
    have h3 : a + b + c = 0 := by linarith
    have h4 : 1 / (a + b + c) = 0 := by
      rw [show a + b + c = 0 by linarith]
      norm_num
    have h5 : 1 / a + 1 / b + 1 / c = 0 := by linarith [h, h4]
    have h6 : a * b + a * c + b * c = 0 := by
      field_simp [ha, hb, hc] at h5 ⊢
      <;> nlinarith
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
      have h8 : a + b + c = 0 := by linarith
      have h9 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
        nlinarith
      rw [h8, h6] at h9
      nlinarith
    have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, h7]
    contradiction
  have h2 : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 := by
    have h_eq : 1 / a + 1 / b + 1 / c = 1 / (a + b + c) := h
    field_simp [ha, hb, hc, h1] at h_eq
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c), sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (a * c - b * c)]
  have h3 : (a + b) * (b + c) * (c + a) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h6 h7
  · -- Case where $a + b = 0$, so $a = -b$
    have h8 : a = -b := by linarith
    have h9 : ∀ k : ℕ, Odd k → a ^ k = -b ^ k := by
      intro k hk
      have h10 : a = -b := h8
      have h11 : a ^ k = (-b) ^ k := by
        rw [show a = -b by linarith]
      have h13 : (-b) ^ k = -b ^ k := by
        have h14 : Odd k := hk
        have h15 : (-b) ^ k = -b ^ k := by
          have h16 : Odd k := h14
          have h17 : (-b) ^ k = -b ^ k := by
            apply Odd.neg_pow
            exact h16
          linarith
        linarith
      rw [h11, h13]
    have h12 : 1 / a ^ k + 1 / b ^ k = 0 := by
      rw [show a ^ k = -b ^ k by apply h9 k hk]
      have hb0 : b ^ k ≠ 0 := by
        apply pow_ne_zero k hb
      field_simp [hb0]
    have h_eq1 : 1 / a ^ k + 1 / b ^ k + 1 / c ^ k = 1 / c ^ k := by
      linarith [h12]
    have h_eq2 : 1 / (a ^ k + b ^ k + c ^ k) = 1 / c ^ k := by
      have h_eq3 : a ^ k + b ^ k = 0 := by
        have h_eq4 : a ^ k = -b ^ k := h9 k hk
        linarith
      have h_eq4 : a ^ k + b ^ k + c ^ k = c ^ k := by
        linarith [h_eq3]
      rw [h_eq4]
    rw [h_eq1, h_eq2]
  · -- Case where $b + c = 0$, so $b = -c$
    have h8 : b = -c := by linarith
    have h9 : ∀ k : ℕ, Odd k → b ^ k = -c ^ k := by
      intro k hk
      have h10 : b = -c := h8
      have h11 : b ^ k = (-c) ^ k := by
        rw [show b = -c by linarith]
      have h13 : (-c) ^ k = -c ^ k := by
        have h14 : Odd k := hk
        have h15 : (-c) ^ k = -c ^ k := by
          have h16 : Odd k := h14
          have h17 : (-c) ^ k = -c ^ k := by
            apply Odd.neg_pow
            exact h16
          linarith
        linarith
      rw [h11, h13]
    have h12 : 1 / b ^ k + 1 / c ^ k = 0 := by
      rw [show b ^ k = -c ^ k by apply h9 k hk]
      have hc0 : c ^ k ≠ 0 := by
        apply pow_ne_zero k hc
      field_simp [hc0]
    have h_eq1 : 1 / a ^ k + 1 / b ^ k + 1 / c ^ k = 1 / a ^ k := by
      linarith [h12]
    have h_eq2 : 1 / (a ^ k + b ^ k + c ^ k) = 1 / a ^ k := by
      have h_eq3 : b ^ k + c ^ k = 0 := by
        have h_eq4 : b ^ k = -c ^ k := h9 k hk
        linarith
      have h_eq4 : a ^ k + b ^ k + c ^ k = a ^ k := by
        linarith [h_eq3]
      rw [h_eq4]
    rw [h_eq1, h_eq2]
  · -- Case where $c + a = 0$, so $c = -a$
    have h8 : c = -a := by linarith
    have h9 : ∀ k : ℕ, Odd k → c ^ k = -a ^ k := by
      intro k hk
      have h10 : c = -a := h8
      have h11 : c ^ k = (-a) ^ k := by
        rw [show c = -a by linarith]
      have h13 : (-a) ^ k = -a ^ k := by
        have h14 : Odd k := hk
        have h15 : (-a) ^ k = -a ^ k := by
          have h16 : Odd k := h14
          have h17 : (-a) ^ k = -a ^ k := by
            apply Odd.neg_pow
            exact h16
          linarith
        linarith
      rw [h11, h13]
    have h12 : 1 / c ^ k + 1 / a ^ k = 0 := by
      rw [show c ^ k = -a ^ k by apply h9 k hk]
      have ha0 : a ^ k ≠ 0 := by
        apply pow_ne_zero k ha
      field_simp [ha0]
    have h_eq1 : 1 / a ^ k + 1 / b ^ k + 1 / c ^ k = 1 / b ^ k := by
      linarith [h12]
    have h_eq2 : 1 / (a ^ k + b ^ k + c ^ k) = 1 / b ^ k := by
      have h_eq3 : a ^ k + c ^ k = 0 := by
        have h_eq4 : c ^ k = -a ^ k := h9 k hk
        linarith
      have h_eq4 : a ^ k + b ^ k + c ^ k = b ^ k := by
        linarith [h_eq3]
      rw [h_eq4]
    rw [h_eq1, h_eq2]