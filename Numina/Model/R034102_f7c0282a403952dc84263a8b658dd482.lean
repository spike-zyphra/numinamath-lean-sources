import Mathlib

open Nat
theorem AMC_Number_theory_98355 (a b c : ℕ) (_ : a ≠ 0) (ha:0≤a∧a≤9) (hb:0≤b∧b≤9) (hc:0≤c∧c≤9)
(h : ∃ n : ℕ, 0 < n ∧ (100 * a + 10 * b + c) = (n ^ 2) + ((1:ℚ) / 3) * ((n + 1) ^ 2 - (n ^ 2)) ∧ (100 * a + 10 * c + b) = (n ^ 2) + ((2:ℚ) / 3) * ((n + 1) ^ 2 - (n ^ 2))) :
a + b + c = 16 := by
  rcases h with ⟨n, hn, he1, he2⟩
  have eq1 : (100 * (a : ℚ) + 10 * (b : ℚ) + (c : ℚ) : ℚ) = (n : ℚ) ^ 2 + (1/3) * ((n + 1 : ℚ) ^ 2 - (n : ℚ) ^ 2) := by
    exact_mod_cast he1
  have eq2 : (100 * (a : ℚ) + 10 * (c : ℚ) + (b : ℚ) : ℚ) = (n : ℚ) ^ 2 + (2/3) * ((n + 1 : ℚ) ^ 2 - (n : ℚ) ^ 2) := by
    exact_mod_cast he2
  have eq3 : 300 * (a : ℚ) + 30 * (b : ℚ) + 3 * (c : ℚ) = 3 * (n : ℚ) ^ 2 + 2 * (n : ℚ) + 1 := by 
    field_simp at eq1 ⊢
    nlinarith
  have eq4 : 300 * (a : ℚ) + 30 * (c : ℚ) + 3 * (b : ℚ) = 3 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 2 := by 
    field_simp at eq2 ⊢
    nlinarith
  have eq5 : 300 * a + 30 * b + 3 * c = 3 * n ^ 2 + 2 * n + 1 := by
    exact_mod_cast eq3
  have eq6 : 300 * a + 30 * c + 3 * b = 3 * n ^ 2 + 4 * n + 2 := by
    exact_mod_cast eq4
  have ha1 : a ≤ 9 := ha.right
  have hb1 : b ≤ 9 := hb.right
  have hc1 : c ≤ 9 := hc.right
  -- Subtract eq5 from eq6: 27c - 27b = 2n + 1
  -- which gives 27 * (c - b) = 2n + 1
  -- so n = (27 * k - 1) / 2, which implies n divisible as integer
  -- testing values, for positive roots, we get $c-b=1$. Thus k=1, $n=13$.
  have eq7 : 27 * (c : ℕ) = 2 * (n : ℕ) + 1 + 27 * (b : ℕ) := by
    omega
  have h7 : c = b + 1 := by
    have h8 : (27 : ℕ) * c = 27 * b + 2 * n + 1 := by 
      omega 
    have h12 : n ≤ 31 := by 
      nlinarith [sq_nonneg ((a : ℕ) ), sq_nonneg ((b : ℕ) ), sq_nonneg ((c : ℕ) ), sq_nonneg ((n : ℕ) ), sq_nonneg ((b - c : ℤ) )
      ] 
    interval_cases n <;> omega 
  rw [show c = b + 1 by linarith [h7] ] at eq6
  -- Now we have equations for $b$ and $c$ in terms of $a$.
  -- Let's write eq5 and eq6 now.
  -- From eq6:
  have eq7 : 300 * a + 30 * (b + 1) + 3 * b = 3 * n ^ 2 + 4 * n + 2 := by
    nlinarith
  -- From eq5:
  have eq8 : 300 * a + 30 * b + 3 * (b + 1) = 3 * n ^ 2 + 2 * n + 1 := by
    nlinarith
  -- Now let's verify $n = 13$, $a = 1, b = 7, c = 8$.
  -- From eq5: $300a + 30b + 3c = 3n^2 + 2n + 1$
  -- From eq6: $300a + 30c + 3b = 3n^2 + 4n + 2$ 
  -- As solved in the algebra, we have $a=1, b=7, c=8, n=13$.
  have h12 : n ≤ 31 := by 
    nlinarith [sq_nonneg ((a : ℕ) ), sq_nonneg ((b : ℕ) ), sq_nonneg ((c : ℕ) ), sq_nonneg ((n : ℕ) ), sq_nonneg ((b - c : ℤ) )
    ] 
  interval_cases n <;> omega