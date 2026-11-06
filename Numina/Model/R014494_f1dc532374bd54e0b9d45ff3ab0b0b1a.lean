import Mathlib

theorem algebra_303455 {a b c : ℤ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a^3 - b^3 - c^3 = 3 * a * b * c) (h2 : a^2 = 2 * (b + c)) :
    (a, b, c) = (2, 1, 1) := by

  have h3 : a % 2 = 0 := by
    have h4 : a ^ 2 % 2 = 0 := by
      have eq1 : a ^ 2 = 2 * (b + c) := h2
      omega
    by_contra h
    push_neg at h
    have h5 : a % 2 = 1 := by
      omega
    have h6 : a ^ 2 % 2 = 1 := by
      have h7 : a % 2 = 1 := h5
      simp [pow_two, Int.add_emod, Int.mul_emod, h7]
    omega

  have h4 : ∃ k : ℤ, a = 2 * k := by
    refine' ⟨a / 2, by omega⟩

  rcases h4 with ⟨k, h7⟩

  have h8 : 2 * k^2 = b + c := by
    rw [show a = 2 * k by linarith [h7]] at h2
    ring_nf at h2
    nlinarith

  have h9 : 8 * k^3 - b^3 - c^3 = 6 * k * b * c := by
    rw [show a = 2 * k by linarith [h7]] at h1
    ring_nf at h1 ⊢
    nlinarith

  have h10 : (2 * k - b - c) * (4 * k^2 + b^2 + c^2 - b * c) = 0 := by
    nlinarith [sq_nonneg (b + c - 2 * k), sq_nonneg (b - c), sq_nonneg (k - 1)]

  cases' (mul_eq_zero.1 h10) with h11 h12
  · -- case 1: 2k - b - c = 0
    have h13 : b + c = 2 * k := by linarith
    have h14 : 2 * k^2 = 2 * k := by
      nlinarith [h8, h13]
    have hk1 : k = 1 := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg (k - 1)]
    have ha2 : a = 2 := by
      nlinarith [h7, hk1]
    have hb1 : b = 1 := by
      have h15 : b + c = 2 := by
        nlinarith [h8, hk1]
      have h16 : b > 0 := by nlinarith
      have h17 : c > 0 := by nlinarith
      have h18 : b ≤ 2 := by nlinarith
      interval_cases b <;> try { omega }
    have hc1 : c = 1 := by
      have h15 : b + c = 2 := by
        nlinarith [h8, hk1]
      have h16 : b > 0 := by nlinarith
      have h17 : c > 0 := by nlinarith
      have h18 : b ≤ 2 := by nlinarith
      have hb1' : b = 1 := hb1
      omega
    simp [Prod.ext_iff, ha2, hb1, hc1]
  · -- case 2: 4k^2 + b^2 + c^2 - b * c = 0
    nlinarith [sq_nonneg (b - c), sq_nonneg (k), sq_nonneg (b + c - 2 * k), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]