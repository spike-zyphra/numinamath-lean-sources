import Mathlib

/- Two numbers are said to be 'relatively prime' if their greatest common factor is 1. How many integers greater than 10 and less than 30 are relatively prime with 28? -/
theorem algebra_20281 : {x : ℕ | 10 < x ∧ x < 30 ∧ Nat.Coprime x 28}.encard = 9 := by
  -- notice that 28 = 2^2x7. so any n ∣ 28, n = 1 or 2 ∣ n or 7 ∣ n
  have h1: ∀n:ℕ, n ≤ 28 → n ∣ 28 →
    (n=1 ∨ 2 ∣ n ∨ 7 ∣ n) := by decide
  --so coprime with 28, is coprime with 2 and 7. or, odd numbers not divided by 7.
  have h2: ∀x:ℕ, (Odd x ∧ ¬ 7 ∣ x) ↔ Nat.Coprime x 28 := by
    intro n
    constructor <;> rw [Nat.coprime_iff_gcd_eq_one] <;> intro h
    · have hh1: Nat.gcd n 28 ∣ 28 := by
        exact Nat.gcd_dvd_right n 28
      have hh2: Nat.gcd n 28 ∣ n := by
        exact Nat.gcd_dvd_left n 28
      have hh3: Nat.gcd n 28 ≤ 28 := by
        apply Nat.gcd_le_right 28 (by norm_num)
      -- by h1, gcd = 1 or divided by 2 or divided by 7
      rcases (h1 (Nat.gcd n 28) hh3 hh1) with g1 | g2 | g7
      · exact g1
      · have heven: Even n := by
          have := Nat.dvd_trans g2 hh2
          exact (even_iff_exists_two_nsmul n).mpr this
        have hodd := h.left
        have hnodd: ¬ Odd n := by
          exact Nat.not_odd_iff_even.mpr heven
        exfalso; apply hnodd hodd
      · have: 7 ∣ n := by
          exact Nat.dvd_trans g7 hh2
        exfalso; apply h.right this
    · have hh1: 2 ∣ 28 := by norm_num
      have hh2: 7 ∣ 28 := by norm_num
      constructor
      · by_contra! neven
        have hh3: 2 ∣ n := by
          have: Even n := by
            exact Nat.not_odd_iff_even.mp neven
          exact even_iff_two_dvd.mp this
        rw [Nat.gcd_eq_iff] at h
        -- if n is even, then n is common factor of n and 28, however gcd is 1, contradiction.
        have := h.right.right 2 hh3 hh1
        contradiction
      · by_contra! ndv7
        rw [Nat.gcd_eq_iff] at h
        -- similarly, if 7 is a common factor, then it divide gcd, but gcd is 1, contradiction.
        have: 7 ∣ 1 := by
          apply h.right.right 7 ndv7 (by norm_num)
        contradiction
  -- so we can rewrite the condition "coprime with 28"
  have h3: {x : ℕ | 10 < x ∧ x < 30 ∧ Nat.Coprime x 28} =
    {x : ℕ | 10 < x ∧ x < 30 ∧ (Odd x ∧ ¬ 7 ∣ x)} := by
    ext n; simp
    intro _ _
    rw [h2 n]
  -- for numbers between 10 and 30, not divided by 7 is to say x ≠ 14,21,28.
  have h4: {x : ℕ | 10 < x ∧ x < 30 ∧ (Odd x ∧ ¬ 7 ∣ x)} =
    {x : ℕ | 10 < x ∧ x < 30 ∧ (Odd x ∧ x ≠ 14 ∧ x ≠ 21 ∧ x ≠ 28)} := by
    ext n; simp
    intro hlb hub _
    constructor; omega; omega
  -- for 14,21,28, only 21 is odd. there are 10 odd numbers between 10 and 30, count 21 off, left 9. so cardinal of the set is 9, and elements are: 11,13,15,17,19; 23,25,27,29
  have h5: {x : ℕ | 10 < x ∧ x < 30 ∧ (Odd x ∧ ¬ 7 ∣ x)} =
    {11,13,15,17,19,23,25,27,29} := by
    rw [h4]
    ext n; simp;
    constructor <;> intro h
    · have hlb := h.left
      have hub := h.right.left
      have hodd := h.right.right.left
      interval_cases n <;> all_goals simp
      <;> contradiction
    · rcases h with hh | hh | hh | hh | hh
        | hh | hh | hh | hh
      <;> rw [hh] <;> simp
      <;> apply Nat.odd_iff.mpr rfl
  rw [h3, h5]
  rw [Set.encard]; simp