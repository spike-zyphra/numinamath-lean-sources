import Mathlib

/- Lemma 1: a + b ≤ ab + 1 for positive integers a and b since (a - 1)(b - 1) ≥ 0. -/
lemma lemma_1 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a + b ≤ a * b + 1 := by nlinarith

/- 8.2. The product of three natural numbers is 60. What is the greatest possible value of their sum?

$$
\text { (4-6 grades) }
$$ -/
theorem number_theory_110174 :
    IsGreatest {a + b + c | (a : ℕ) (b : ℕ) (c : ℕ) (_ : a * b * c = 60)} 62 := by
  constructor
  . -- We achieve 62 by setting a = 60, b = 1, c = 1
    use 60, 1, 1
  . -- We show 62 is the maximum
    rintro - ⟨a, b, c, h, rfl⟩
    -- We show that a, b, c are positive
    have ⟨ha, hb, hc⟩ : 0 < a ∧ 0 < b ∧ 0 < c := by
      refine ⟨?_, ?_, ?_⟩
      all_goals
        refine Nat.zero_lt_of_ne_zero ?_
        rintro rfl
        simp at h
    -- So a + b + c ≤ ab + c + 1 ≤ abc + 2
    calc a + b + c
      _ ≤ a * b + 1 + c := (add_le_add_iff_right c).mpr (lemma_1 a b ha hb)
      _ = a * b + c + 1 := add_right_comm (a * b) 1 c
      _ ≤ a * b * c + 1 + 1 := (add_le_add_iff_right 1).mpr (lemma_1 (a * b) c (mul_pos ha hb) hc)
      _ = 62 := h ▸ rfl
