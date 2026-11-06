import Mathlib

/- Let a, b, c, d, e be positive integers with a + b + c + d + e = 2010 and let M be the largest of the sum a+b, b+c, c+d and d+e. What is the smallest possible value of M?
(A) 670
(B) 671
(C) 802
(D) 803
(E) 804 -/
theorem algebra_94263 : IsLeast {M : ℕ | ∃ (a b c d e :ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
a + b + c + d + e = 2010 ∧ M = (a+b) ⊔ (b+c) ⊔ (c+d) ⊔ (d+e)} 671 := by
  constructor
  -- to prove 671 is a possible value of M, use 669, 1, 670, 1, 669 for a, b, c, d, e
  . use 669, 1, 670, 1, 669
    norm_num
  -- to prove 671 is a lower bound, use the fact that a + b ≤ m, c + d ≤ m, e ≤ d + e ≤ m to get 2010 = 3m, hence 671 ≤ m
  . intro m hm_in
    obtain ⟨a, b, c, d, e, ha_pos, hb_pos, hc_pos, hd_pos, he_pos, hsum, hm⟩ := hm_in
    have hm₁ : a+b ≤ m := by simp [hm]
    have hm₂ : c+d ≤ m := by simp [hm]
    have hm₃ : e ≤ m := by
      calc
        e ≤ d + e := by linarith
        _ ≤ m := by simp [hm]
    omega