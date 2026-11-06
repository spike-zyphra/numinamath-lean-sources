import Mathlib

/- Find all integer solutions of the equation $2 x^{6}+y^{7}=11$. -/
theorem number_theory_604752 : {(x, y) : ℤ × ℤ | 2 * x ^ 6 + y ^ 7 = 11} = ∅ := by
  ext ⟨x, y⟩
  suffices ¬2 * x ^ 6 + y ^ 7 = 11 by simpa
  intro h
  --   There are no solutions.
  --   The hardest part of the problem is to determine a modulus $m$ that would yield a contradiction.
  -- There should be few sixth and seventh powers modulo $m$,
  -- hence, a natural choice is $6 \cdot 7+1=43$. Luckily, it is a prime.
  replace h : 2 * x ^ 6 + y ^ 7 ≡ 11 [ZMOD 43] := by congr
  --   Indeed,
  -- $$
  -- \begin{aligned}
  -- 2 x^{6} \bmod 43 & \in\{0,2,8,22,27,32,39,42\}, \\
  -- \end{aligned}
  -- $$
  have hx : (2 * x ^ 6) % 43 ∈ ({0,2,8,22,27,32,39,42} : Finset ℤ) := by
    have : (2 * x ^ 6) % 43 = (2 * (x % 43) ^ 6) % 43 := by
      change _ ≡ _ [ZMOD 43]
      gcongr
      exact Int.ModEq.symm (Int.mod_modEq x 43)
    rw [this]
    have : 0 ≤ x % 43 := Int.emod_nonneg _ (by norm_num)
    have : x % 43 < 43 := Int.emod_lt_of_pos _ (by norm_num)
    simp [-EuclideanDomain.mod_eq_zero]
    interval_cases x % 43 <;> norm_num
  -- $$
  -- \begin{aligned}
  -- 11-y^{7} \bmod 43 & \in\{4,5,10,11,12,17,18\},
  -- \end{aligned}
  -- $$
  have hy : (11 - y ^ 7) % 43 ∈ ({4,5,10,11,12,17,18} : Finset ℤ) := by
    have : (11 - y ^ 7) % 43 = (11 - (y % 43) ^ 7) % 43 := by
      change _ ≡ _ [ZMOD 43]
      gcongr
      exact Int.ModEq.symm (Int.mod_modEq y 43)
    rw [this]
    have : 0 ≤ y % 43 := Int.emod_nonneg _ (by norm_num)
    have : y % 43 < 43 := Int.emod_lt_of_pos _ (by norm_num)
    simp [-EuclideanDomain.mod_eq_zero]
    interval_cases y % 43 <;> norm_num
  -- Suffices to show `((2 * x ^ 6) % 43 - (11 - y ^ 7) % 43) % 43 ≠ 0`.
  suffices ((2 * x ^ 6) % 43 - (11 - y ^ 7) % 43) % 43 ≠ 0 by
    replace h : 2 * x ^ 6 + y ^ 7 - 11 ≡ 0 [ZMOD 43] := by convert h.sub_right 11
    revert this
    simp [-EuclideanDomain.mod_eq_zero]
    change _ ≡ 0 [ZMOD 43]
    refine Int.ModEq.trans ?_ h
    rw [sub_eq_add_neg, add_sub_assoc]
    gcongr
    . exact Int.mod_modEq (2 * x ^ 6) 43
    . rw [show y^7-11=-(11-y^7) by ring]
      gcongr
      exact Int.mod_modEq (11 - y ^ 7) 43
  -- and these sets do not intersect.
  simp [-EuclideanDomain.mod_eq_zero] at hx hy
  casesm* _ ∨ _
  all_goals
    rename_i h1 h2
    norm_num [h1, h2]
