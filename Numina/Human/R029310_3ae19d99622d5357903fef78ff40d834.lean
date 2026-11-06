import Mathlib

/- Find the smallest value of $n > 2$ such that the equation $1^2 + 2^2 + 3^2 + \ldots + n^2 = m^2$ holds for some integer $m$. -/
theorem number_theory_613237:
    let sum (n : ℕ) := ∑ i ∈ Finset.range (n + 1) , i ^ 2
    IsLeast {n | 2 < n ∧ ∃ m, sum n = m^2} 24 :=
by
  intro sum
  -- The sum of the squares of the first $n$ natural numbers is given by the formula: $S = \frac{n(n + 1)(2n + 1)}{6}$.
  -- We first prove in rational number type, since it is easier to process division.
  have sum_eq' : ∀ n : ℕ, (sum n : ℚ) = n * (n+1) * (2*n+1) / 6 := by
    intro n
    induction n with
    | zero => simp[sum]
    | succ n ih =>
        simp[sum]
        have : (∑ i ∈ Finset.range (n + 1 + 1), i ^ 2 : ℚ)=
              (∑ i ∈ Finset.range (n+1), i ^ 2) + (n+1)^2 := by
          rw[Finset.sum_range_succ]
          push_cast
          simp
        rw [this]
        simp [sum] at ih
        push_cast
        rw [ih]
        ring_nf
  -- We can now prove the result in natural number type.
  have sum_eq : ∀ n : ℕ, sum n = n * (n+1) * (2*n+1) / 6 := by
    intros n
    have := sum_eq' n
    -- If the division is a natural number, then $b$ divides $a$.
    have : ∀ (n a b: ℕ), b ≠ 0 → (n : ℚ) = a / b → b ∣ a := by
      intros n a b b0 h
      use n
      qify
      apply_fun (fun (x : ℚ) => x * b) at h
      ring_nf at h
      rewrite [mul_comm (b : ℚ) a, mul_assoc] at h
      rw [Rat.mul_inv_cancel] at h
      linarith
      qify at b0
      assumption
    have : 6 ∣ n * (n + 1) * (2 * n + 1) := by
      apply this (sum n)
      . simp
      . push_cast; apply sum_eq'
    zify
    qify
    rw [Rat.intCast_div]
    push_cast
    apply sum_eq'
    zify at this
    assumption
  -- Now back to the original problem.
  constructor
  . simp
    use 70
    rewrite [sum_eq]
    simp
  . simp [lowerBounds]
    by_contra H
    push_neg at H
    let ⟨a, al, sqrt_suma, sqrt_suma_eq, ah⟩ := H

    have H : a ∈ List.range' 3 21 := by simp; constructor <;> assumption
    simp only [List.range'] at H

    -- We need to find the smallest $n &gt; 2$ that satisfies this equation.
    -- Test values of $n$ starting from $3$:
    --    - For $n = 3$: $3 \cdot 4 \cdot 7 = 84$, which is not a perfect square.
    --    - For $n = 4$: $4 \cdot 5 \cdot 9 = 180$, which is not a perfect square.
    --    - Continue testing values until $n = 24$.
    -- For $n = 24$: $24 \cdot 25 \cdot 49 = 29400$.
    -- Check if $29400$ is a perfect square: $29400 = 6 \cdot 4900 = 6 \cdot 70^2$.
    -- Therefore, $29400 = 6m^2$ implies $m^2 = 4900$ and $m = 70$.
    -- The smallest value of $n &gt; 2$ that satisfies the equation is \boxed{24}.
    generalize aH : a = a'
    repeat
      rcases H
      let suma := sum a'

      have : IsSquare suma := by
        use sqrt_suma
        simp [suma, ←aH]
        ring_nf
        assumption

      have : ¬ IsSquare suma := by
        -- Note that you can use `decide` here, but it is too slow.
        -- So we use `Nat.sqrt` to speed up the process.
        simp [suma, ←aH, sum_eq]
        simp [IsSquare]
        intro x h
        have : Nat.sqrt suma = x := by
          simp [suma, ←aH, sum_eq]
          rw [h]
          apply Nat.sqrt_eq
        simp [suma, ←aH, sum_eq] at this
        simp [Nat.sqrt, Nat.sqrt.iter] at this
        subst this
        simp at h

      tauto
      rename List.Mem _ _ => H
    nomatch H
