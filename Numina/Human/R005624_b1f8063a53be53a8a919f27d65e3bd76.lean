import Mathlib
/- How many positive integers less than 100 are relatively prime to 200? (Two numbers are relatively prime if their greatest common factor is 1 .) -/
theorem number_theory_609161 : {n ∈ Finset.range 100| Nat.Coprime 200 n}.card = 40:= by
  -- Define a set equality: numbers coprime to 200 are the same as numbers coprime to 100
  have h1 : {n ∈ Finset.range 100| Nat.Coprime 200 n} = {a ∈ Finset.range 100 | Nat.Coprime 100 a}:= by exact rfl
  -- Rewrite the goal using the set equality
  rw [h1]
  -- Use the totient function theorem: the count of numbers coprime to n equals φ(n)
  rw [←Nat.totient_eq_card_coprime]
  -- Automatically solve the goal using the decide tactic
  decide
