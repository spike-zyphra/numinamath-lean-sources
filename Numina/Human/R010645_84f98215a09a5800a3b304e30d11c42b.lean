import Mathlib

/- 3. In the sequence $\left\{a_{n}\right\}$, for $1 \leqslant n \leqslant 5$, we have $a_{n}=n^{2}$; and for all positive integers $n$, we have $a_{n+5}+a_{n+1}=a_{n+4}+a_{n}$. Then $a_{2023}=$ $\qquad$ . -/
theorem algebra_165122 (a : ℕ → ℕ) (h₀ : ∀ n ∈ Finset.Icc 1 5, a n = n ^ 2)
    (h₁ : ∀ n > 0, a (n + 5) + a (n + 1) = a (n + 4) + a n) :
    a 2023 = 17 := by
  -- Establish the value of a_1 = 1 using the first hypothesis
  have ha1 : a 1 = 1 := by
    specialize h₀ 1 (by norm_num)
    norm_num at h₀
    exact h₀
  -- Establish the value of a_2 = 4 using the first hypothesis
  have ha2 : a 2 = 4 := by
    specialize h₀ 2 (by norm_num)
    norm_num at h₀
    exact h₀
  -- Establish the value of a_3 = 9 using the first hypothesis
  have ha3 : a 3 = 9 := by
    specialize h₀ 3 (by norm_num)
    norm_num at h₀
    exact h₀
  -- Establish the value of a_5 = 25 using the first hypothesis
  have ha5 : a 5 = 25 := by
    specialize h₀ 5 (by norm_num)
    norm_num at h₀
    exact h₀
  -- Calculate a_6 = 22 using the recurrence relation and previously established values
  have ha6 : a 6 = 22 := by
    have h := h₁ 1 (by norm_num)
    norm_num [ha1, ha2, ha5] at h
    omega
  -- Calculate a_7 = 17 using the recurrence relation and previously established values
  have ha7 : a 7 = 17 := by
    have h := h₁ 2 (by norm_num)
    norm_num [ha2, ha3, ha6] at h
    omega
  -- Prove that a_2023 = 17 by showing the sequence has a period of 8
  have h2023 : a 2023 = 17 := by
    -- Prove that the sequence has period 8: a_(n+8) = a_n for all positive integers n
    have h1 : ∀ n > 0, a (n + 8) = a n := by
      intro n hn
      have h1 := h₁ n hn
      have h2 := h₁ (n + 1) (by linarith)
      have h3 := h₁ (n + 2) (by linarith)
      have h4 := h₁ (n + 3) (by linarith)
      -- Derive equations by applying the recurrence relation multiple times
      have eq2 : a (n + 6) + a (n + 2) = a (n + 5) + a (n + 1) := by linarith [h2]
      have eq3 : a (n + 7) + a (n + 3) = a (n + 6) + a (n + 2) := by linarith [h3]
      have eq4 : a (n + 8) + a (n + 4) = a (n + 7) + a (n + 3) := by linarith [h4]
      omega
    -- Use the periodicity to show that a_2023 = a_7
    have h2023eq : a 2023 = a 7 := by
      calc
        a 2023 = a (7 + 8 * 252) := by norm_num
        _ = a 7 := by
          norm_num [h1]
    rw [h2023eq, ha7]
  exact h2023
