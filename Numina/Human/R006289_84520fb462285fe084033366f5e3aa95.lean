import Mathlib

open Nat

/- Let $P$ be a prime number. Show that there exist three prime numbers $p_1, p_2, q_1$, which are distinct from each other and also distinct from $P$, such that if $x = p_1 p_2$ and $y = q_1 P$, then $x > y$, $x$ and $y$ have the same number of natural divisors, and the sum of all natural divisors of $x$ (including 1 and $x$) is less than the sum of all natural divisors of $y$ (including 1 and $y$). For the purpose of this problem, assume $P=17$. -/
theorem number_theory_635560 {P : ℕ} (hP1 : P = 17) :
    ∃ p1 p2 q1 : ℕ, p1.Prime ∧ p2.Prime ∧ q1.Prime ∧ p1 ≠ p2 ∧ p1 ≠ q1 ∧ p2 ≠ q1 ∧ p1 ≠ P ∧ p2 ≠ P ∧ q1 ≠ P ∧
    let x := p1 * p2
    let y := q1 * P
    x > y ∧ x.divisors.card = y.divisors.card ∧ ∑ d ∈ x.divisors, d < ∑ d ∈ y.divisors, d :=
by
  use 5, 7, 2
  have r1 : (35 : ℕ).divisors = {1,5,7,35} := by decide
  have r2 : (2 * P).divisors = {1,2,17,34} := by rw[hP1]; decide
  repeat
    constructor
    try norm_num
    try swap
  all_goals
    try rw [r1]
    try rw [r2]
    try rw[hP1]
    try simp
