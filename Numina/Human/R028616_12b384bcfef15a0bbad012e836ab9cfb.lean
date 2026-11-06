import Mathlib

/- A sequence of three real numbers forms an arithmetic progression with a first term of 9. If 2 is added to the second term and 2020 is added to the third term, the three resulting numbers form a geometric progression. What is the smallest possible value for the third term in the geometric progression?
(A) 1
(B) 4
(C) 36
(D) 49
(E) 81
 -/

theorem algebra_95135 : let isValid (a d r : ℝ) := (a = 9) ∧ (a + d + 2 = r * a ∧ a + 2 * d + 20 = r * (a + d + 2));
((isValid a d r) → a + 2*d + 20 ≥ 1) ∧ (∃ a d r, (isValid a d r) ∧  a + 2*d + 20 = 1) := by
  -- split to two goals, proving >= 1 and proving 1 is attainable
  constructor
  -- first case: break out all hypothesis
  . intro ⟨ha, hb⟩
    rw [ha] at hb
    have ⟨hb1, hb2⟩ := hb
    -- in geometric series (a * r)^2 = a * (a * r^2), use that and replace all occurences of r with only those of a,d
    have hd : (11 + d)^2 = 9 * (2*d + 29) := by calc
      (11 + d)^2 = (r * 9)^2 := by rw [← hb1]; ring
      _ = 9 * (r * (r * 9)) := by ring
      _ = 9 * (r * (9+d+2)) := by rw [hb1]
      _ = 9 * (2*d + 29) := by rw [← hb2]; ring
    -- factorize last statement into (d+14) * (d-10) = 0, so d = -14 or d = 10
    have hd: (d+14) * (d-10) = 0 := by linarith
    have hd: d+14 = 0 ∨ d-10 = 0 := mul_eq_zero.1 hd
    -- for both values of d, compute to prove a + 2*d + 20 >= 1
    cases hd with
    | inl h14 =>
      have h14: d = -14 := by linarith
      rw [ha, h14]
      norm_num
    | inr h10 =>
      have h10: d = 10 := by linarith
      rw [ha, h10]
      norm_num
  -- second case: provide a = 9, d = -14, r = -1/3 to show that they generate a + 2 *d + 20 = 1 and required conditions are met
  . use 9
    use -14
    use -1.0/3.0
    constructor
    . norm_num
    . norm_num