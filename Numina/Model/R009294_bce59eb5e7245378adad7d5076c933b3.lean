import Mathlib
theorem number_theory_609179 (p q r : ℕ) : (p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ p * q * r = 989 * 1001 * 1007 + 320) ↔ p = 991 ∧ q = 997 ∧ r = 1009:= by
  constructor
  · -- Forward direction: assume the conjunction and prove the equality of p, q, r
    rintro ⟨hp, hq, hr, h1, h2, h3⟩
    have h4 : p * q * r = 991 * 997 * 1009 := by
      norm_num at h3 ⊢
      linarith
    have g1 : Nat.Prime 991:= by norm_num
    have g2 : Nat.Prime 997:= by norm_num
    have g3 : Nat.Prime 1009:= by norm_num
    have g4 : 1009 ∣ p * q * r:= by rw [h4] ; omega
    apply (Nat.Prime.dvd_mul g3).mp at g4
    rcases g4 with g4 | g4
    · -- Case where 1009 divides p*q
      apply (Nat.Prime.dvd_mul g3).mp at g4
      rcases g4 with g4 | g4
      · -- Case where 1009 divides p
        replace g4 : 1009 = 1 ∨ 1009 = p:= by exact (Nat.dvd_prime hp).mp g4
        simp at g4
        rw [←g4] at h4
        have g5 : q * r = 991 * 997:= by
          linarith
        have g6 : 997 ∣ q * r:= by rw [g5] ; omega
        apply (Nat.Prime.dvd_mul g2).mp at g6
        rcases g6 with g6 | g6
        · -- Case where 997 divides q
          replace g6 : 997 = 1 ∨ 997 = q:= by exact (Nat.dvd_prime hq).mp g6
          simp at g6
          rw [←g6] at g5
          have g7 : r = 991 := by
            nlinarith
          have g8 : r < q := by
            linarith [g7, g6]
          linarith
        · -- Case where 997 divides r
          replace g6 : 997 = 1 ∨ 997 = r:= by exact (Nat.dvd_prime hr).mp g6
          simp at g6
          rw [←g6] at g5
          have g7 : q = 991 := by
            nlinarith
          have g8 : q < r := by
            linarith [g7, g6]
          linarith
      · -- Case where 1009 divides q
        replace g4 : 1009 = 1 ∨ 1009 = q:= by exact (Nat.dvd_prime hq).mp g4
        simp at g4
        rw [←g4] at h4
        have g5 : p * r = 991 * 997:= by
          linarith
        have g6 : 997 ∣ p * r:= by rw [g5] ; omega
        apply (Nat.Prime.dvd_mul g2).mp at g6
        rcases g6 with g6 | g6
        · -- Case where 997 divides p
          replace g6 : 997 = 1 ∨ 997 = p:= by exact (Nat.dvd_prime hp).mp g6
          simp at g6
          rw [←g6] at g5
          have g7 : r = 991 := by
            nlinarith
          have g8 : r < p := by
            linarith [g7, g6]
          linarith
        · -- Case where 997 divides r
          replace g6 : 997 = 1 ∨ 997 = r:= by exact (Nat.dvd_prime hr).mp g6
          simp at g6
          rw [←g6] at g5
          have g7 : p = 991 := by
            nlinarith
          have g8 : p < q := by
            linarith [g7, g4]
          linarith
    · -- Case where 1009 divides r
      replace g4 : 1009 = 1 ∨ 1009 = r:= by exact (Nat.dvd_prime hr).mp g4
      simp at g4
      rw [←g4] at h4
      have g5 : p * q = 991 * 997:= by
        linarith
      have g6 : 997 ∣ p * q:= by rw [g5] ; omega
      apply (Nat.Prime.dvd_mul g2).mp at g6
      rcases g6 with g6 | g6
      · -- Case where 997 divides p
        replace g6 : 997 = 1 ∨ 997 = p:= by exact (Nat.dvd_prime hp).mp g6
        simp at g6
        rw [←g6] at g5
        have g7 : q = 991 := by
          nlinarith
        have g8 : q < r := by
          linarith [g7, g4]
        constructor
        · linarith
        constructor
        · linarith
        · linarith
      · -- Case where 997 divides q
        replace g6 : 997 = 1 ∨ 997 = q:= by exact (Nat.dvd_prime hq).mp g6
        simp at g6
        rw [←g6] at g5
        have g7 : p = 991 := by
          nlinarith
        have g8 : p < q := by
          linarith [g7, g6]
        constructor
        · linarith
        constructor
        · linarith
        · linarith
  · -- Backward direction: assume the equality and prove the conjunction
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num