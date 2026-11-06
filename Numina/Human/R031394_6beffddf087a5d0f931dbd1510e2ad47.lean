import Mathlib

/- Prover que l'équation

$$
a^{3}+b^{5}+c^{7}+d^{11}=e^{13}
$$

admet une infinité de solutions en entiers strictement positifs. -/
/- Prouver que l'équation

$$
a^{3}+b^{5}+c^{7}+d^{11}=e^{13}
$$

admet une infinité de solutions en entiers strictement positifs. -/
theorem number_theory_607476 :
    Set.Infinite {(a, b, c, d, e) : ℤ × ℤ × ℤ × ℤ × ℤ |
      a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a^3 + b^5 + c^7 + d^11 = e^13} := by
  -- It suffices to prove that there exists a solution in positive integers.
  suffices H : ∃ a b c d e : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a^3 + b^5 + c^7 + d^11 = e^13
  by
    -- If so, let the solution be (a, b, c, d, e).
    rcases H with ⟨a, b, c, d, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    -- (a * k ^ (5 * 7 * 11 * 13), b * k ^ (3 * 7 * 11 * 13), c * k ^ (3 * 5 * 11 * 13), d * k ^ (3 * 5 * 7 * 13), e * k ^ (3 * 5 * 7 * 11)) is also a solution for any k > 0.
    -- So we can define a function f : ℕ → ℤ ^ 5 which is injective and whose image is the set of solutions.
    let f (n : ℕ) : ℤ × ℤ × ℤ × ℤ × ℤ := (a * (n + 1) ^ (5 * 7 * 11 * 13), b * (n + 1) ^ (3 * 7 * 11 * 13), c * (n + 1) ^ (3 * 5 * 11 * 13), d * (n + 1) ^ (3 * 5 * 7 * 13), e * (n + 1) ^ (3 * 5 * 7 * 11))
    -- f is clearly injective.
    have hf : f.Injective := by
      intro n m h
      simp [f, ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃, ne_of_gt h₄, ne_of_gt h₅] at h
      norm_cast at h
      simp at h
      exact h
    -- We now need to prove that the image of f is in the set of solutions.
    apply Set.infinite_of_injective_forall_mem hf
    intro n
    -- Which follows from a simple computation.
    simp [f, h₁, h₂, h₃, h₄, h₅, mul_pow, ← pow_mul, ← add_mul, h₆]
  -- Now we need to find a solution, we can assume that a, b, c, d, e are powers of 2.
  -- We set x := 2 to avoid auto computation in Lean.
  obtain ⟨x, hx⟩ : ∃ (x : ℤ), x = 2 := ⟨2, rfl⟩
  have hx' : x > 0 := by positivity
  -- Let a = x ^ (5 * 7 * 11), b = x ^ (3 * 7 * 11), c = x ^ (3 * 5 * 11), d = x ^ (3 * 5 * 7), e = x ^ 89.
  use x ^ (5 * 7 * 11), x ^ (3 * 7 * 11), x ^ (3 * 5 * 11), x ^ (3 * 5 * 7), x ^ 89
  -- We need to prove that this is a solution.
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity, ?_⟩
  -- LHS = x ^ 1155 * 4, RHS = x ^ 1157
  -- As 4 = x ^ 2, we are done.
  ring_nf
  rw [show 4 = x ^ 2 by simp [hx]]
  ring
