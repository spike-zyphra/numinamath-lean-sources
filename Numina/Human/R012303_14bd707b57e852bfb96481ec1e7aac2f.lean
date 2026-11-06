import Mathlib

set_option linter.unusedVariables false

/- Find the three-digit positive integer abc​ whose representation in base nine is bca, where a, b, and c are 
(not necessarily distinct) digits. -/
theorem number_theory_98609 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 8) (hb : 0 ≤ b ∧ b ≤ 8) (hc : 0 ≤ c ∧ c ≤ 8) (h : 100 * a + 10 * b + c = 81 * b + 9 * c + a) :
a = 2 ∧ b = 2 ∧ c = 7 := by {
  -- We start by establishing the congruence 28*a ≡ 8*c [MOD 71], which follows immediately from rearranging our assumption.
  -- The reason to use 71 is that it eliminates the dependence on b.
  have h1 : 28*a ≡ 8*c [MOD 71] := by {
    rw [←Int.natCast_modEq_iff]
    have h' : (100 : ℤ)*a  + 10*b + c = 81*b + 9*c + a := by norm_cast
    have h'' : (99 : ℤ)*a = 71*b + 8 * c := by {rw [←sub_eq_zero]; rw [←sub_eq_zero] at h'; rw [← h']; ring}
    calc (28 : ℤ)*a ≡ 99*a [ZMOD 71] := by {rw [Int.modEq_iff_dvd, ←sub_mul]; norm_num}
                  _ ≡ 71*b + 8*c [ZMOD 71] := by rw [h'']
                  _ ≡ 8*c [ZMOD 71] := by { rw [Int.modEq_iff_dvd]; ring_nf; norm_num}
  }
  -- From there we can immediately deduce the values of a and c.
  have ha' : a = 2 := by omega
  have hc' : c = 7 := by omega
  constructor
  exact ha'
  constructor
  -- Plugging the values of a and c into our original equation gives us b.
  rw [ha',hc'] at h
  simp at h
  linarith
  exact hc'
}