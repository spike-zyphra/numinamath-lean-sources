import Mathlib

/-In the sequence $\left\{x_{n}\right\}$, $x_{1}>3$, and $x_{n}=\frac{3 x_{n-1}^{2}-x_{n-1}}{4\left(x_{n-1}-1\right)}(n=2,3, \cdots)$, prove that: $3<x_{n+1}<x_{n}(n=$ $1,2, \cdots)$.-/
theorem algebra_188770 {x : ℕ → ℝ} (hx1 : x 1 > 3)
    (hxn : ∀ n ≥ 2, x n = (3 * (x (n - 1))^2 - x (n - 1))/(4 * (x (n - 1) - 1))) :
    ∀ n ≥ 1, 3 < x (n + 1) ∧ x (n + 1) < x n := by
  intro n hn
  -- We prove the statement by mathematical induction.
  induction n with
  | zero => 
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    -- the following two cases are solved in the similar way。
    cases n with
    | zero =>
      -- First we prove that $3<x_{2}$ through the equality
      -- $$ x_{k+1}-3=\frac{\left(x_{k}-3\right)\left(3 x_{k}-4\right)}{4\left(x_{k}-1\right)} $$
      -- and the fact that $x_{1}>3$.
      have h1 : 3 < x 2 := by 
        have h2 : x 2 = (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) := by 
          specialize hxn 2 (by norm_num)
          simpa using hxn
        have h3 : x 1 > 3 := hx1
        have h4 : 4 * (x 1 - 1) > 0 := by 
          nlinarith
        have h5 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) > 3 := by
          have h6 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) - 3 > 0 := by
            have h7 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) - 3 = (3 * (x 1) ^ 2 - x 1 - 12 * (x 1 - 1)) / (4 * (x 1 - 1)) := by
              field_simp [(show 4 * (x 1 - 1) ≠ 0 by nlinarith)]
              ring
            rw [h7]
            have h8 : 3 * (x 1) ^ 2 - x 1 - 12 * (x 1 - 1) > 0 := by
              nlinarith [sq_nonneg (x 1 - 3), sq_nonneg (x 1 - 4 / 3)]
            have h9 : (3 * (x 1) ^ 2 - x 1 - 12 * (x 1 - 1)) / (4 * (x 1 - 1)) > 0 := by
              apply div_pos 
              · linarith 
              · nlinarith 
            linarith
          linarith [h6]
        rw [h2]
        linarith [h5]
      -- Then we prove that $x_{2}<x_{1}$ from the equality
      -- $$\quad x_{n+1}-x_{n}=\frac{-x_{n}\left(x_{n}-3\right)}{4\left(x_{n}-1\right)} $$
      have h2' : x 2 < x 1 := by 
        have h10 : x 2 = (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) := by 
          specialize hxn 2 (by norm_num)
          simpa using hxn
        rw [h10]
        have h11 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) < x 1 := by 
          have h12 : 4 * (x 1 - 1) > 0 := by 
            nlinarith
          have h13 : (3 * (x 1) ^ 2 - x 1) < x 1 * (4 * (x 1 - 1)) := by 
            nlinarith [sq_nonneg (x 1 - 3)]
          have h15 : (3 * (x 1) ^ 2 - x 1) / (4 * (x 1 - 1)) < x 1 := by 
            have h16 : (3 * (x 1) ^ 2 - x 1) < (4 * (x 1 - 1)) * x 1 := by linarith
            have h17 : 4 * (x 1 - 1) > 0 := by nlinarith
            apply (div_lt_iff₀ (by linarith)).mpr 
            nlinarith
          linarith [h15]
        linarith [h11]
      exact ⟨h1, h2'⟩
    | succ n =>
      -- We can prove the second cases similarly as follows. Just need to replace $x_2$ by $x_{n+1}$ and $x_1$ by $x_n$.
      have ih' : 3 < x (n + 1 + 1) ∧ x (n + 1 + 1) < x (n + 1) := ih (by linarith)
      have h1 : 3 < x (n + 1 + 1 + 1) := by 
        have h2 : x (n + 1 + 1 + 1) = (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) := by 
          specialize hxn (n + 1 + 1 + 1) (by linarith)
          simpa using hxn
        have h3 : x (n + 1 + 1) > 3 := ih'.left
        have h4 : 4 * (x (n + 1 + 1) - 1) > 0 := by 
          nlinarith
        have h5 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) > 3 := by 
          have h6 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) - 3 > 0 := by 
            have h7 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) - 3 = (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1) - 12 * (x (n + 1 + 1) - 1)) / (4 * (x (n + 1 + 1) - 1)) := by 
              field_simp [(show 4 * (x (n + 1 + 1) - 1) ≠ 0 by nlinarith)]
              ring
            rw [h7]
            have h8 : 3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1) - 12 * (x (n + 1 + 1) - 1) > 0 := by 
              nlinarith [sq_nonneg (x (n + 1 + 1) - 3), sq_nonneg (x (n + 1 + 1) - 4 / 3)]
            have h9 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1) - 12 * (x (n + 1 + 1) - 1)) / (4 * (x (n + 1 + 1) - 1)) > 0 := by 
              apply div_pos 
              · linarith 
              · nlinarith 
            linarith
          linarith [h6]
        rw [h2]
        linarith [h5]
      have h2' : x (n + 1 + 1 + 1) < x (n + 1 + 1) := by 
        have h10 : x (n + 1 + 1 + 1) = (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) := by 
          specialize hxn (n + 1 + 1 + 1) (by linarith)
          simpa using hxn
        rw [h10]
        have h11 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) < x (n + 1 + 1) := by 
          have h12 : 4 * (x (n + 1 + 1) - 1) > 0 := by 
            nlinarith
          have h13 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) < x (n + 1 + 1) * (4 * (x (n + 1 + 1) - 1)) := by 
            nlinarith [sq_nonneg (x (n + 1 + 1) - 3)]
          have h14 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) / (4 * (x (n + 1 + 1) - 1)) < x (n + 1 + 1) := by 
            have h15 : (3 * (x (n + 1 + 1)) ^ 2 - x (n + 1 + 1)) < (4 * (x (n + 1 + 1) - 1)) * x (n + 1 + 1) := by linarith
            have h16 : 4 * (x (n + 1 + 1) - 1) > 0 := by nlinarith
            apply (div_lt_iff₀ (by linarith)).mpr 
            nlinarith
          linarith [h14]
        linarith [h11]
      exact ⟨h1, h2'⟩