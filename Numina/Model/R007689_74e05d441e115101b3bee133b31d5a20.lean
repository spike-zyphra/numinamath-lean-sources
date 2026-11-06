import Mathlib

set_option maxRecDepth 400000
theorem number_theory_609925: {n: ℕ | 1 ≤ n ∧ n ≤ 100 ∧ (Nat.divisors (10 * n)).card = 3 * (Nat.divisors (n)).card}.encard = 28 := by 
  have h1 : {n: ℕ | 1 ≤ n ∧ n ≤ 100 ∧ (Nat.divisors (10 * n)).card = 3 * (Nat.divisors (n)).card} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 100 ∧ (Nat.divisors (10 * n)).card = 3 * (Nat.divisors (n)).card) (Finset.Icc 0 100) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { native_decide }
  all_goals
    try { rfl }
    try { omega }
  all_goals
    try { native_decide }
    try { omega }