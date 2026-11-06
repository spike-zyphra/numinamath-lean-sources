import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_305002 {p q : ℝ → ℝ → Prop}
  (hp : p = λ m n => 2 < m + n ∧ m + n < 4 ∧ 0 < m * n ∧ m * n < 3)
  (hq : q = λ m n => 0 < m ∧ m < 1 ∧ 2 < n ∧ n < 3) :
  ¬ (∀ m n, p m n → q m n) ∧ (∀ m n, q m n → p m n) := by
  -- To prove that p is not sufficient for q, find a counterexample
  have h1 : ¬ (∀ m n, p m n → q m n) := by
    rw [hp, hq]
    intro h
    -- Let's test m = 2, n = 0.5
    specialize h 2 (0.5 : ℝ)
    norm_num at h 
  -- To prove that p is necessary for q, show that q implies p
  have h2 : ∀ m n, q m n → p m n := by 
    rw [hp, hq]
    intros m n hqn
    rcases hqn with ⟨hm1, hm2, hn1, hn2⟩
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith
  -- Conclude that p is necessary but not sufficient
  exact ⟨h1, h2⟩