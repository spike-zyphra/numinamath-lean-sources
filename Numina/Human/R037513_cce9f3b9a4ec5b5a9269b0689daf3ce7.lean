import Mathlib

/- Positive integers $a, b$ and $c$ satisfy the system of equations

(a * b - 1) ^ 2 = c * (a ^ 2 + b ^ 2) + a * b + 1
a ^ 2 + b ^ 2 = c ^ 2 + a * b

(a) Prove that $c+1$ is a perfect square.
(b) Find all such triples $(a, b, c)$.

Answer: (b) $a=b=c=3$. -/
theorem algebra_605293 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h1 : (a * b - 1) ^ 2 = c * (a ^ 2 + b ^ 2) + a * b + 1)
(h2 : a ^ 2 + b ^ 2 = c ^ 2 + a * b):
    IsSquare (c + 1) ∧ (a = 3 ∧ b = 3 ∧ c = 3) := by
    replace h1: a ^ 2 * b ^ 2 - 2 * a * b = c * (a ^ 2 + b ^ 2) + a * b := by nlinarith [h1]
    replace h2: a * b = a ^ 2 + b ^ 2 - c ^ 2 := by nlinarith [h2]
    rw [h2] at h1
    replace h1: a ^ 2 * b ^ 2 + c ^ 2 = (c + 1) * (a ^ 2 + b ^ 2) + 2 * a * b := by nlinarith [h1, h2]
    replace h1: (a * b + c) ^ 2 = (c + 1) * (a + b) ^ 2 := by nlinarith [h1]
    have dvd: (a + b) ^ 2 ∣ (a * b + c) ^ 2 := by
        rw [h1]
        simp
    have dvd': a + b ∣ a * b + c := by
        rw [Int.pow_dvd_pow_iff] at dvd
        exact dvd
        norm_num
    have sq: IsSquare (c + 1) := by
        rw [IsSquare.eq_1]
        use (a * b + c) / (a + b)
        have o: ((a * b + c) / (a + b)) * ((a * b + c) / (a + b)) = (a * b + c) ^ 2 / (a + b) ^ 2 := by
            qify
            have o1: ↑((a * b + c) / (a + b)) = ((a * b + c): ℚ) / (a + b) := by
                rw [Int.cast_div]
                simp
                exact dvd'
                norm_cast
                omega
            rw [o1]
            have o2: ↑((a * b + c) ^ 2 / (a + b) ^ 2) = ((a * b + c): ℚ) ^ 2 / (a + b) ^ 2 := by
                rw [Int.cast_div]
                simp
                exact dvd
                norm_cast
                nlinarith
            rw [o2]
            field_simp
            ring
        rw [o,h1]
        field_simp
    simp [sq]
    rw [IsSquare.eq_1] at sq
    obtain ⟨e, he⟩ := sq
    set d:= |e| with hd'
    have hd: c + 1 = d ^ 2 := by
        simp [hd',he]
        ring
    have ld: 0 ≤ d := by
        apply abs_nonneg
    clear_value d
    clear hd' he
    simp [hd] at h1
    rw [show d ^ 2 * (a + b) ^ 2 = (d * (a + b)) ^ 2 by ring] at h1
    rw [sq_eq_sq_iff_abs_eq_abs] at h1
    have o1: |a * b + c| = a * b + c := by
        apply abs_of_nonneg
        nlinarith
    have o2: |d * (a + b)| = d * (a + b) := by
        apply abs_of_nonneg
        nlinarith
    rw [o1,o2] at h1
    clear o1 o2
    rw [show c = d ^ 2 - 1 by omega] at h1
    replace h1: (a - d) * (b - d) = 1 := by
        replace h1: a * b + d ^ 2 - d * (a + b) = 1 := by linarith
        rw [show (a - d) * (b - d) = a * b + d ^ 2 - d * (a + b) by ring]
        rw [h1]
    by_cases l: d ≤ b
    -- the case where d ≤ b
    . replace l: 0 ≤ b - d := by omega
      have fb:= Int.eq_one_of_mul_eq_one_left l h1
      simp [fb] at h1
      replace fb: b = a := by omega
      replace h1: a = d + 1 := by omega
      simp [fb] at h2
      ring_nf at h2
      replace h2: a ^ 2 = c ^ 2 := by omega
      rw [sq_eq_sq_iff_abs_eq_abs] at h2
      rw [show |a| = a by apply abs_of_nonneg; nlinarith] at h2
      rw [show |c| = c by apply abs_of_nonneg; nlinarith] at h2
      replace h2: c = d + 1 := by omega
      simp [h2] at hd
      ring_nf at hd
      replace hd: (d + 1) * (d - 2) = 0 := by nlinarith [hd]
      simp at hd
      rcases hd with hd | hd
      . omega
      . omega
    -- the case where d > b
    . replace l: 0 ≤ d - b := by omega
      replace h1: (d - a) * (d - b) = 1 := by nlinarith [h1]
      have fb:= Int.eq_one_of_mul_eq_one_left l h1
      simp [fb] at h1
      replace fb: b = a := by omega
      replace h1: a = d - 1 := by omega
      simp [fb] at h2
      ring_nf at h2
      replace h2: a ^ 2 = c ^ 2 := by omega
      rw [sq_eq_sq_iff_abs_eq_abs] at h2
      rw [show |a| = a by apply abs_of_nonneg; nlinarith] at h2
      rw [show |c| = c by apply abs_of_nonneg; nlinarith] at h2
      replace h2: c = d - 1 := by omega
      simp [h2] at hd
      ring_nf at hd
      replace hd: d * (d - 1) = 0 := by nlinarith [hd]
      simp at hd
      rcases hd with hd | hd
      . omega
      . omega