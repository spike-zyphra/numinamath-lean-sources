import Mathlib

/- Let $S$ be the set of all positive factors of 6000. -/
def S : Finset ℕ := Nat.divisors 6000

/- We can compute the set of all positive factors of 6000. -/
lemma hS : S = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 24, 25, 30, 40, 48, 50, 60, 75, 80, 100, 120, 125, 150, 200, 240, 250, 300, 375, 400, 500, 600, 750, 1000, 1200, 1500, 2000, 3000, 6000} := by native_decide

/- We can compute the number of elements in the set of all positive factors of 6000, that is $40$. -/
lemma hScard : Finset.card S = 40 := by native_decide

/- Let $S$ be the set of all positive factors of 6000 . What is the probability of a random quadruple $(a, b, c, d) \in S^{4}$ satisfies

$$
\operatorname{lcm}(\operatorname{gcd}(a, b), \operatorname{gcd}(c, d))=\operatorname{gcd}(\operatorname{lcm}(a, b), \operatorname{lcm}(c, d)) ?
$$ -/
theorem number_theory_609996 :
    ((S ×ˢ S ×ˢ S ×ˢ S).filter (fun (a, b, c, d) => (a.gcd b).lcm (c.gcd d) = (a.lcm b).gcd (c.lcm d))).card / (S ×ˢ S ×ˢ S ×ˢ S).card = (41 / 512 : ℚ) := by
  -- Simplify the expression using the lemmas.
  rw [Finset.card_product, Finset.card_product, Finset.card_product, hScard, hS]
  -- Let's compute by brute force. It takes less than 5 seconds on the server.
  native_decide
