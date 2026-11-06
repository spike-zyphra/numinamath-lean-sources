import Mathlib

/- In this problem, we generalize the rule given in problem 24 to find the squares
  of integers that have a final digit of $B$ in base $2B$, where $B$ is a positive integer.
  We need to demonstrate that the base $2B$ representation of the integer
  \((a_n a_{n-1} \ldots a_1 a_0)_{2B}\) begins with the digits of the base $2B$
  representation of the integer \((a_n a_{n-1} \ldots a_1 a_0)_{2B} \left[
  \left(a_n a_{n-1} \ldots a_1 a_0\right)_{2B} + 1\right]\) and ends with the
  digits \(B/2\) and 0 when \(B\) is even, and the digits \((B-1)/2\) and \(B\)
  when \(B\) is odd. -/
theorem number_theory_4478 (B x : ℕ) :
    (Even B → (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + B / 2 * (2 * B)) ∧
    (Odd B → (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + (B - 1) / 2 * (2 * B) + B) := by
  refine ⟨fun ⟨b, h⟩ => ?_, fun ⟨b, h⟩ => ?_⟩
  -- B is even.
  · simp only [h]
    ring_nf
    rw [Nat.mul_div_cancel _ (by simp)]
    ring
  -- B is odd.
  · simp only [h]
    ring_nf
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (by simp)]
    ring
