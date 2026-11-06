import Mathlib

open Polynomial

/- Show that there does not exist a real polynomial $P$ such that $P(n)=\sqrt[3]{n^{2}+1}$ for all positive integers $n$. -/
theorem algebra_112573 :
    ¬∃ P : Polynomial ℝ, ∀ n : ℕ, 0 < n → P.eval (n : ℝ) = (n ^ 2 + 1) ^ ((1 : ℝ) / 3) := by
  -- Assume that there exists a real polynomial p such that p(n) = (n ^ 2 + 1) ^ (1/3) for all positive integers.
  by_contra h
  replace ⟨p, h⟩ := h
  -- Show that p^3 = X^2 + 1.
  have hp3 : p ^ 3 = X ^ 2 + 1 := by
    -- It is enough to show that p^3 and X^2 + 1 evaluate to the same values on an infinite set.
    apply eq_of_infinite_eval_eq
    -- Let s = {n + 1 | n ∈ ℕ}.
    set s : Set ℝ := (fun n : ℕ => (n + 1 : ℝ)) '' Set.univ
    -- Clearly, s is infinite.
    have hs_inf : s.Infinite := by
      apply Set.Infinite.image _ Set.infinite_univ
      simp [Set.InjOn]
    -- Show that p^3 and X^2 + 1 evaluate to the same values on s.
    apply Set.Infinite.mono _ hs_inf
    intro x
    simp [s]
    intro n hx
    rw [← hx]
    -- We need to show p(n + 1)^3 = (n + 1)^2 + 1.
    have eq := h (n + 1) (by omega)
    push_cast at eq
    -- We know that p(n + 1) = ((n + 1)^2 + 1)^(1 / 3).
    -- So p(n + 1)^3 = (n + 1)^2 + 1.
    rw [eq, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    rw [Real.rpow_inv_natCast_pow _ (by norm_num)]
    positivity
  -- Show that p ≠ 0.
  have hp0 : p ≠ 0 := by
    -- Suppose that p = 0.
    contrapose! h
    -- Then 0 = p(1) ≠ (1 + 1)^(1/3).
    use 1, zero_lt_one
    simp [h]
    apply ne_of_lt
    positivity
  -- We have p^3 = X^2 + 1.
  -- The degree of p^3 is 3 * p.degree, the degree of X^2 + 1 is 2.
  -- This is impossible since 3 does not divide 2.
  apply_fun degree at hp3
  rw [degree_pow, show (X ^ 2 + 1 : ℝ[X]).degree = 2 by compute_degree!] at hp3
  rw [degree_eq_natDegree hp0] at hp3
  simp at hp3
  norm_cast at hp3
  omega