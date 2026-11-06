import Mathlib

/-To make lemonade, I use a ratio of $7$ parts water to $1$ part lemon juice. If I want to make a gallon of lemonade, and there are four quarts in a gallon, how many quarts of water do I need? Write your answer as a proper or improper fraction.-/
theorem algebra_13913 (total_parts : ℕ) (h : total_parts = 7 + 1) :
    (7 / total_parts : ℚ) * 4 = 7 / 2 := by rw [h]; ring_nf
