import Mathlib.Tactic

/- determine -/ abbrev solution_a : ℕ := 40
/- determine -/ abbrev solution_b : ℕ := 34

/- (a) How many positive integer factors does  $6000$  have?

(b) How many positive integer factors of  $6000$  are not perfect squares? -/
theorem number_theory_8617
    (n : ℕ)
    (hn : n = 6000) :
    (solution_a = n.divisors.card) ∧
    (solution_b = (n.divisors.filter (fun d ↦ ¬ IsSquare d)).card) := by
  simp [solution_a, solution_b, hn]
  -- (Nat.divisors 6000).card and (Finset.filter (fun d ↦ ¬IsSquare d) (Nat.divisors 6000)).card are computable natural numbers.
  -- In order to prove that they equal to some concrete numbers, we can use the "native_decide" tactic.
  constructor <;> native_decide