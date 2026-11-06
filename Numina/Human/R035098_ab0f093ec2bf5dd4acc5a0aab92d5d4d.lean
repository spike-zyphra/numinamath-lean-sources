import Mathlib

open Finset

/-- Back in 1930, Tillie had to memorize her multiplication facts from $0 \times 0$ to $12 \times
12$. The multiplication table she was given had rows and columns labeled with the factors, and the
products formed the body of the table. To the nearest hundredth, what fraction of the numbers in
the body of the table are odd?

$\textbf{(A)}\; 0.21 \qquad\textbf{(B)}\; 0.25 \qquad\textbf{(C)}\; 0.46 \qquad\textbf{(D)}\; 0.50 \qquad\textbf{(E)}\; 0.75$ -/
theorem number_theory_96886 (s : Finset (ℕ × ℕ)) (hs : s = range 13 ×ˢ range 13)
    (t : Finset (ℕ × ℕ)) (ht : t = {p ∈ s | Odd (p.1 * p.2)}) :
    (t.card : ℚ) / s.card = 36 / 169 := by

  -- Let $s$ be the whole table, and $t$ be the subset of locations with odd products.

  -- We want to show that the ratio of the number of odd products to the total number of products
  -- is $36/169$. It is enough to show that the number of odd products is $36$ and the total number
  -- of products is $169$.
  suffices t.card = 36 ∧ s.card = 169 by rw [this.1, this.2]; norm_num

  -- The total number of products is $13^2 = 169$.
  refine ⟨?_, by simp [hs]⟩

  -- Let's show that the number of odd products is $36$.

  -- We know that a product is odd if and only if both its factors are odd.
  have (a b : ℕ) : Odd (a * b) ↔ Odd a ∧ Odd b := by rw [Nat.odd_mul]

  -- Therefore, $t$ is the set of pairs $(a, b)$ such that $a$ and $b$ are both odd.
  replace ht : t = {p ∈ s | Odd (p.1) ∧ Odd (p.2)} := by
    ext ⟨a, b⟩
    simp [ht]
    intro h
    rw [this]

  -- Which means, $t$ is just the cartesion product of the set $p$ with itself, where $p$ is the set
  -- of odd numbers from $1$ to $13$.
  let p := {a ∈ range 13 | Odd a}
  replace ht : t = p ×ˢ p := by
    ext ⟨a, b⟩
    simp [ht, p, hs]
    tauto

  -- We know that the cardinality of $p$ is $6$. Therefore, the cardinality of $t$ is $6^2 = 36$.
  have p_card : p.card = 6 := by decide
  rw [ht, card_product, p_card]