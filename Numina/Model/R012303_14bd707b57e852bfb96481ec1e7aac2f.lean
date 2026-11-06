import Mathlib

set_option linter.unusedVariables false

theorem number_theory_98609 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 8) (hb : 0 ≤ b ∧ b ≤ 8) (hc : 0 ≤ c ∧ c ≤ 8) (h : 100 * a + 10 * b + c = 81 * b + 9 * c + a) :
a = 2 ∧ b = 2 ∧ c = 7 := by
  have h1 : 28*a ≡ 8*c [MOD 71] := by {
    rw [←Int.natCast_modEq_iff]
    have h' : (100 : ℤ)*a  + 10*b + c = 81*b + 9*c + a := by norm_cast
    have h'' : (99 : ℤ)*a = 71*b + 8 * c := by {rw [←sub_eq_zero]; rw [←sub_eq_zero] at h'; rw [← h']; ring}
    calc (28 : ℤ)*a ≡ 99*a [ZMOD 71] := by {rw [Int.modEq_iff_dvd, ←sub_mul]; norm_num}
                 _ ≡ 71*b + 8*c [ZMOD 71] := by rw [h'']
                 _ ≡ 8 * ↑c [ZMOD 71] := by
                  have h3 : (71 * (b : ℤ) + 8 * (c : ℤ)) % 71 = 8 * (c : ℤ) % 71 := by
                    omega
                  rw [Int.modEq_iff_dvd] at *
                  omega
  }
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> omega