import Mathlib

/-For a positive integer $n$, let $p(n)$ denote the product of the positive integer factors of $n$. Determine the number of factors $n$ of 2310 for which $p(n)$ is a perfect square.-/
theorem number_theory_608919 {p : ℕ → ℕ} (hp : ∀n, p n = ∏ i ∈ n.divisors, i) :
    Set.ncard {n : ℕ | n ∈ Nat.divisors 2310 ∧ IsSquare (p n)} = 27 := by
  have h₁ : {n : ℕ | n ∈ Nat.divisors 2310 ∧ IsSquare (p n)} = Finset.filter (fun n => IsSquare (∏ i ∈ n.divisors, i)) (Nat.divisors 2310) := by
    ext x; simp only [hp, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true, Set.mem_setOf_eq, Finset.coe_filter, and_congr_right_iff]
  rw [h₁, Set.ncard_coe_Finset]
  native_decide
