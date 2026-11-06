import Mathlib

/- Determine all nonnegative integers $n$ having two distinct positive divisors with the same distance from $\tfrac{n}{3}$.
(Richard Henner) -/

theorem number_theory_82568: {n: ℤ | 0 < n ∧ ∃ x y: ℤ, x ∣ n ∧ y ∣ n ∧ 0 < x ∧ x < (n: ℚ) / 3 ∧
(n: ℚ) / 3 < y ∧ y - (n: ℚ) / 3 = (n: ℚ) / 3 - x } = {n: ℤ | ∃ m: ℤ, 0 < m ∧ n = 6 * m} := by

  ext n
  constructor
  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at *
    rcases h with ⟨ln, h⟩
    obtain ⟨x, y, h⟩ := h
    rcases h with ⟨dx, dy, hx1, hx2, hy1, h⟩
    -- we first show that n is a multiple of 3
    have d3: 3 ∣ n := by
      by_contra! o
      replace h: x + y = (2 * n) / (3: ℚ) := by
        nlinarith
      replace h: 3 * (x + y) = 2 * n := by
        field_simp at h
        norm_cast at h
        omega
      have i: 3 ∣ 2 * n := by
        rw [← h]
        simp
      have h1: IsCoprime (3: ℤ) 2 := by norm_num
      have s: 3 ∣ n := by
        apply IsCoprime.dvd_of_dvd_mul_left h1 i
      tauto
    apply exists_eq_mul_right_of_dvd at d3
    obtain ⟨k, hk⟩ := d3
    have lk: 0 < k := by omega
    simp [hk] at *
    norm_cast at h
    apply exists_eq_mul_right_of_dvd at dy
    obtain ⟨q, hq⟩ := dy
    have u1: k < y := by
      nlinarith
    have u2: y < 2 * k := by nlinarith
    have lq1: q < 3 := by
      nlinarith
    have lq2: 1 < q := by
      nlinarith
    have sq: q = 2 := by omega
    simp [sq] at *
    have d2: 2 ∣ 3 * k := by
      rw [hq]
      simp
    replace d2: 2 ∣ k := by
      have h1: IsCoprime (2: ℤ) 3 := by norm_num
      apply IsCoprime.dvd_of_dvd_mul_left h1 d2
    apply exists_eq_mul_right_of_dvd at d2
    obtain ⟨m, hm⟩ := d2
    use m
    constructor
    .
      omega
    .
      rw [hm]
      omega


  -- the backward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨m, hm⟩ := h
    rcases hm with ⟨hn, h⟩
    simp only [h]
    constructor
    .
      omega
    .
      use m
      use 3 * m
      constructor
      .
        simp
      .
        constructor
        .
          rw [show 6 * m = 2 * (3 * m) by ring]
          simp
        .
          constructor
          .
            omega
          .
            constructor
            .
              rw [lt_div_iff₀]
              norm_cast
              linarith
              norm_num
            .
              constructor
              .
                rw [div_lt_iff₀]
                norm_cast
                linarith
                norm_num
              .
                rw [show ↑(3 * m) = 3 * (m: ℚ) by norm_cast]
                rw [show ↑(6 * m) = 6 * (m: ℚ) by norm_cast]
                field_simp
                ring