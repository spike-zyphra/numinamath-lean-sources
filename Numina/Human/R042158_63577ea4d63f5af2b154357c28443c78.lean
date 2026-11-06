import Mathlib

/-For a real number r, the quadratics x ^ 2 + (r - 1) * x + 6 and
x ^ 2 + (2 * r + 1) * x + 22 have a commom real root. The sum of the possible values of r
can be expressed as a/b, where a, b are relatively prime positive integers. Compute 100 * a + b-/

theorem algebra_610217 {a b: ℕ} (hab: Nat.Coprime a b) (hb: 0 < b)
(h: ∑ᶠ r ∈ {r: ℝ | ∃ x: ℝ, x ^ 2 + (r - 1) * x + 6 = 0 ∧ x ^ 2 + (2 * r + 1) * x + 22 = 0}, r = (a: ℝ) / b):
100 * a + b = 405 := by
  have h_eq: {r: ℝ | ∃ x: ℝ, x ^ 2 + (r - 1) * x + 6 = 0 ∧ x ^ 2 + (2 * r + 1) * x + 22 = 0} = {6, -26 / 5} := by
    ext r
    constructor
    -- the forward direction
    . intro h
      simp at h
      simp
      obtain ⟨x,h⟩ := h
      rcases h with ⟨h1,h2⟩
      have h3: (r + 2) * x + 16 = 0 := by
        nlinarith
      have ne: r + 2 ≠ 0 := by
        by_contra! no
        simp [no] at h3
      have h4: x = -16 / (r + 2) := by
         field_simp
         nlinarith
      replace h3: (r + 2) * x = -16 := by nlinarith
      replace h1: (r + 2) * (x ^ 2 + (r - 1) * x + 6) = 0 := by
        rw [h1]
        simp
      rw [show (r + 2) * (x ^ 2 + (r - 1) * x + 6) = (r + 2) * x * x + (r - 1) * ((r + 2) * x) + 6 * r + 12 by ring] at h1
      rw [h3] at h1
      ring_nf at h1
      rw [h4] at h1
      field_simp at h1
      ring_nf at h1
      rw [show 312 + (r * 8 - r ^ 2 * 10) = - 10 * (r - 6) * (r + 26 / 5) by ring] at h1
      simp at h1
      rcases h1 with h1 | h1
      . left
        linarith
      . right
        linarith
    -- the backward direction
    . intro h
      simp at *
      rcases h with h | h
      all_goals simp [h]; ring_nf
      . use -2
        norm_num
      . use 5
        norm_num

  -- finally, we derive the value of a/b
  rw [h_eq] at h
  rw [finsum_mem_eq_finite_toFinset_sum] at h
  have h_sum:  ∑ i ∈ {6, -26 / 5}, i = (4: ℝ) / 5 := by
    simp [Finset.sum]
    norm_num
  simp at h
  rw [h_sum] at h
  clear * - h hb hab
  replace h: (5: ℝ) * ↑a = 4 * b := by
    field_simp at h
    rw [h]
    ring
  norm_cast at h
  have d1: 4 ∣ 5 * a := by
    rw [h]
    omega
  replace d1: 4 ∣ a := by
    apply Nat.Coprime.dvd_of_dvd_mul_left at d1
    exact d1
    norm_num
  apply exists_eq_mul_right_of_dvd at d1
  obtain ⟨c,hc⟩ := d1
  simp [hc] at h
  replace h: b = 5 * c := by
    nlinarith [h]
  have l: c = 1 := by
    by_contra! no
    rw [hc,h] at hab
    absurd hab
    have dgt1: 1 < c := by omega
    have hm: c ∣4 * c := by
      apply Nat.dvd_mul_left
    have hn: c ∣5 * c := by
      apply Nat.dvd_mul_left
    have o:= Nat.not_coprime_of_dvd_of_dvd dgt1 hm hn
    exact o
  simp [l] at hc h
  simp [hc,h]
  simp