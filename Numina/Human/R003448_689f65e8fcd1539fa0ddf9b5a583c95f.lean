import Mathlib

open Real

-- If a = 1, a + b + c = 3, a^2 - a ≥ 1 - b * c then b = c = 1.
lemma lemma_1 (a b c : ℝ) (ha : a = 1) (h1 : a + b + c = 3) (h2 : a^2 - a ≥ 1 - b * c) : b = 1 ∧ c = 1 := by
  subst ha
  -- It is enough to show that b = 1 (c = 3 - b - a = 1).
  suffices b = 1 by simp [this]; linarith
  -- c = 2 - b.
  have hc : c = 2 - b := by linarith
  subst c
  -- h2 implies that (b - 1)^2 ≤ 0.
  have hb : (b - 1)^2 ≤ 0^2 := by linear_combination h2
  -- We conclude that b = 1.
  rw [sq_le_sq, abs_zero, abs_nonpos_iff] at hb
  linarith

-- If a + b + c = 3, a^2 - a ≥ 1 - b * c, and b^2 - b ≥ 1 - a * c then
-- (a - 1) * (b - 1) ≤ 0.
lemma lemma_2 (a b c : ℝ) (h1 : a + b + c = 3) (h2 : a^2 - a ≥ 1 - b * c) (h3 : b^2 - b ≥ 1 - a * c) :
    (a - 1) * (b - 1) ≤ 0 := by
  rw [← ge_iff_le]
  -- We have
  -- 2 * (1 - a - b + a * b)
  --   = ((1 - b * c) - (a^2 - a)) + ((1 - a * c) - (b^2 - b))
  --   ≤ 0.
  have ineq : 2 * (1 - a - b + a * b) ≤ 0 := calc
    2 * (1 - a - b + a * b) = 2 - c * (a + b) + a + b - a^2 - b^2 := by
      rw [show c = 3 - (a + b) by linarith]
      ring
    _ = ((1 - b * c) - (a^2 - a)) + ((1 - a * c) - (b^2 - b)) := by
      ring
    _ ≤ 0 := by linarith
  -- We conclude that (a - 1) * (b - 1) = 1 - a - b + a * b ≤ 0.
  linear_combination ineq / 2

/- 6. Find all triples of positive numbers $a, b, c$, satisfying the conditions $a+b+c=3, a^{2}-a \geqslant 1-b c$, $b^{2}-b \geqslant 1-a c, \quad c^{2}-c \geqslant 1-a b$. -/
theorem inequalities_183491 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 3) (h2 : a^2 - a ≥ 1 - b * c) (h3 : b^2 - b ≥ 1 - a * c)
    (h4 : c^2 - c ≥ 1 - a * b) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  -- lemma_2 implies (a - 1) * (b - 1) ≤ 0.
  have hab := lemma_2 a b c h1 h2 h3
  -- lemma_2 implies (a - 1) * (c - 1) ≤ 0.
  have hac := lemma_2 a c b (by linarith) (by linarith) (by linarith)
  -- lemma_2 implies (b - 1) * (c - 1) ≤ 0.
  have hbc := lemma_2 b c a (by linarith) (by linarith) (by linarith)
  -- Consider 3 cases: a < 1, a = 1, or a > 1.
  rcases lt_trichotomy a 1 with h | h | h
  · -- If a < 1 then (a - 1) * (b - 1) ≤ 0 implies that 1 ≤ b.
    have hb : 1 ≤ b := by
      contrapose! hab
      apply mul_pos_of_neg_of_neg <;> linarith
    -- (a - 1) * (c - 1) ≤ 0 implies that 1 ≤ c.
    have hc : 1 ≤ c := by
      contrapose! hac
      apply mul_pos_of_neg_of_neg <;> linarith
    rw [le_iff_eq_or_lt] at hb hc
    cases' hb with hb hb
    · -- If b = 1 then lemma_1 implies that a = 1, a contradiction.
      linarith [lemma_1 b a c hb.symm (by linarith) (by linarith)]
    cases' hc with hc hc
    · -- If c = 1 then lemma_1 implies that a = 1, a contradiction.
      linarith [lemma_1 c a b hc.symm (by linarith) (by linarith)]
    -- Assume htat 1 < b and 1 < c then
    -- (b - 1) * (c - 1) ≤ 0 is impossible.
    contrapose! hbc
    apply mul_pos (by linarith) (by linarith)
  · -- If a = 1 then lemma_1 implies that b = c = 1.
    simp [h]
    exact lemma_1 a b c h h1 h2
  · -- If a > 1 then (a - 1) * (b - 1) ≤ 0 implies that b ≤ 1.
    have hb : b ≤ 1 := by
      contrapose! hab
      apply mul_pos <;> linarith
    -- (a - 1) * (c - 1) ≤ 0 implies that c ≤ 1.
    have hc : c ≤ 1 := by
      contrapose! hac
      apply mul_pos <;> linarith
    rw [le_iff_eq_or_lt] at hb hc
    cases' hb with hb hb
    · -- If b = 1 then lemma_1 implies that a = 1, a contradiction.
      linarith [lemma_1 b a c hb (by linarith) (by linarith)]
    cases' hc with hc hc
    · -- If c = 1 then lemma_1 implies that a = 1, a contradiction.
      linarith [lemma_1 c a b hc (by linarith) (by linarith)]
    -- Assume that b < 1 and c < 1 then
    -- (b - 1) * (c - 1) ≤ 0 is impossible.
    contrapose! hbc
    apply mul_pos_of_neg_of_neg (by linarith) (by linarith)