import Mathlib

/- 1. For which positive integers \( m \) are the following statements true?
   a) \( 27 \equiv 5 \pmod{m} \) -/
theorem number_theory_4650_1 (hmp : m > 0) :
    (Nat.ModEq m 27 5) ↔ ((m=1) ∨ (m=2) ∨ (m=11) ∨ (m=22)) := by
  --condiser both side
  constructor
  -- now we need to prove  m = 1 or m = 2 or m = 11 or m = 22
  intro h
  -- name the assumption with h
  by_cases hm:m>27
  -- consider the cases such that m>27
  have : 27=5 := by apply Nat.ModEq.eq_of_lt_of_lt;exact h;linarith;linarith
  -- we can find a contradition in this cases
  trivial
  -- Use the false.Elim
  interval_cases m
  -- Consider the other cases
  any_goals (reduce at h)
  -- for all cases ,calcuate the mod
  any_goals (simp at h)
  -- simp at all
  any_goals (aesop)
  -- Use ATP to finish the proof

/- 1. For which positive integers \( m \) are the following statements true?
   b) \( 1000 \equiv 1 \pmod{m} \) -/
theorem number_theory_4650_2 (hmp : m > 0) :
    (Nat.ModEq m 1000 1) ↔ ((m=1) ∨ (m=3) ∨ (m=9) ∨ (m=27) ∨
    (m=37) ∨ (m=111) ∨ (m=333) ∨ (m=999)) := by
  --condiser both side
  constructor
   -- now we need to prove m = 1 ∨ m = 3 ∨ m = 9 ∨ m = 27 ∨ m = 37 ∨ m = 111 ∨ m = 333 ∨ m = 999
  intro h
    -- name the assumption with h
  by_cases hm:m>1000
    -- consider the case such that m>1000
  have : 1000=1 := by apply Nat.ModEq.eq_of_lt_of_lt;exact h;linarith;linarith
  trivial
    -- we can find a contradition in this cases
  interval_cases m
    -- Consider the other cases
  any_goals (reduce at h)
  -- for all cases ,calcuate the mod
  any_goals (simp at h)
  -- simp at all
  any_goals (aesop)
  -- Use ATP to finish the proof


/- 1. For which positive integers \( m \) are the following statements true?
   c) \( 1331 \equiv 0 \pmod{m} \) -/
theorem number_theory_4650_3 (hmp : m > 0) :
    (Nat.ModEq m 1331 0) ↔ ((m=1) ∨ (m=1331) ∨(m=11) ∨ (m=121)):= by
 --condiser both side
  constructor
   -- now we need to prove (m=1) ∨ (m=1331) ∨(m=11) ∨ (m=121)
  intro h
    -- name the assumption with h
  by_cases hm:m>1331
 -- consider the case such that m>1331
  have : 1331=0 := by apply Nat.ModEq.eq_of_lt_of_lt;exact h;linarith;linarith
  trivial
    -- we can find a contradition in this cases
  interval_cases m
    -- Consider the other cases
  any_goals (reduce at h)
  -- for all cases ,calcuate the mod
  any_goals (simp at h)
  -- simp at all
  any_goals (aesop)
  -- Use ATP to finish the proof
