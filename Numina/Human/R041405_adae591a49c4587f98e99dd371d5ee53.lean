import Mathlib

/-A base-10 integer $n$ can be represented as $32_a$ in one base and $23_b$ in another base, where $a$ and $b$ are any integer bases larger than 3. What is the smallest possible sum $a$+$b$?-/
theorem number_theory_22874 :
    IsLeast {x | ∃ n a b, n > 3 ∧ a > 3 ∧ b > 3 ∧ x = a + b ∧
      Nat.digits a n = [2, 3] ∧ Nat.digits b n = [3, 2]} 12 := by
  -- Let S = Set, this can simplify the notation.
  obtain ⟨S, hS⟩ := show ∃s, s = {x | ∃ n a b, n > 3 ∧ a > 3 ∧ b > 3 ∧ x = a + b ∧
      Nat.digits a n = [2, 3] ∧ Nat.digits b n = [3, 2]} by simp
  rw [hS.symm]
  -- In Lean4, to prove that 12 is the least element of S, we need to show that 12 is in S and that any element of S is greater than or equal to 12.
  have _12_in_S : 12 ∈ S := by
    rw [hS]
    simp
    use 17
    simp
    use 5
    simp
    use 7
    simp
  unfold IsLeast
  use _12_in_S
  apply (le_csInf_iff' (Set.nonempty_of_mem _12_in_S)).mp
  apply le_csInf (Set.nonempty_of_mem _12_in_S)
  rw [hS]
  simp
  intro x n hn₁ a ha₁ b hb₁ hab ha₂ hb₂
  -- We start by changing the expressions to base 10 in terms of $a$ and $b$. We also know that the two expressions should be equal since they represent the same number. \begin{align*}
  -- 32_a&=23_b\quad\Rightarrow\\
  -- 3\cdot a+2\cdot 1&=2\cdot b +3\cdot1\quad\Rightarrow\\
  -- 3a+2&=2b+3\quad\Rightarrow\\
  -- 3a&=2b+1.
  -- \end{align*}For the smallest sum $a+b$, we would want the smallest bases $a$ and $b$. $a$ and $b$ must be greater than 3, so we'll let $a=4$ and that means $12=2b+1$ and $b$ is not an integer. Next we try $a=5$ and that means $15=2b+1$ and $b=7$. That means our sum is $5+7=\boxed{12}$. We can check that both expressions work: $32_5=3\cdot5+2=17$ and $23_7=2\cdot7+3=17$.
  have ha₂ : n = 3 * a + 2 := by
    have : n = Nat.ofDigits a [2, 3] := by
      rw [ha₂.symm, Eq.comm]
      exact Nat.ofDigits_digits _ _
    rw [this, Nat.ofDigits]
    simp
    linarith
  have hb₂ : n = 2 * b + 3 := by
    have : n = Nat.ofDigits b [3, 2] := by
      rw [hb₂.symm, Eq.comm]
      exact Nat.ofDigits_digits _ _
    rw [this, Nat.ofDigits]
    simp
    linarith
  have hab₂ : 3 * a = 2 * b + 1 := by linarith
  -- Also, it makes sense that $a=5$ works while $a=4$ does not since $3a$ must be odd for $b$ to be an integer ($3a-1=2b$ means $3a$ must be even after subtracting 1), and for $3a$ to be odd, $a$ must also be odd.
  -- Alternatively, we can just try different bases. The smallest possible value for $a$ and $b$ is 4. If we let $b=4$, we'd need a smaller base for $a$ (since we have $3\cdot a\approx2\cdot b$), which isn't possible. When we let $a=4$, we get $32_4=14$ and try to find a $b$ such that $23_b=14$. That means $2b+3=14$ and $b$ is not an integer. When we let $a=5$, we get $32_5=17$ and try to find a $b$ such that $23_b=17$. If $2b+3=17$, then $b=7$ and we still get $a+b=\boxed{12}$.
  omega
