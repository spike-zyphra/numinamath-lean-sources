import Mathlib

/- What integer $n$ satisfies $0\le n<18$ and $$n\equiv -11213141\pmod{18}~?$$ -/
theorem number_theory_19326 : {n : ℤ | 0 ≤ n ∧ n < 18 ∧ n ≡ -11213141 [ZMOD 18]} = {13} := by
  ext n
  -- split the goal into two
  constructor
  . -- prove the forward direction
    intro hn
    simp at hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    -- rewrite the congruence modulo condition
    have h1 := Int.modEq_iff_add_fac.mp hn3
    -- introduce k
    rcases h1 with ⟨k, hk⟩
    -- use the inequalities of n to find the value of k
    have hk1 : k = -622953 := by linarith
    -- trivial substitution
    have hnn : n = 13 := by linarith
    trivial
  . -- prove the backward direction
    intro hn
    -- simplify the goal
    simp at hn ⊢
    refine ⟨(by linarith), (by linarith), ?_⟩
    -- substitute the value of n
    rw [hn]
    rfl
