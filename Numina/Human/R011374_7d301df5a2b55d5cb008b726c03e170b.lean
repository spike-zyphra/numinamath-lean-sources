import Mathlib

open Polynomial
/- The adjacent two terms ${{a}_{n}}$ and ${{a}_{n+1}}$ of the sequence $\left{ {{a}_{n}} \right}$ are the two roots of the quadratic equation ${{x}^{2}}-3nx+{{c}_{n}}=0\left( n=1,2,3,\cdots \right)$. When ${{a}_{1}}=1$, find ${{c}_{n}}$.-/
theorem algebra_622967 {a c : ℕ → ℝ}
    (h₀ : ∀ n : ℕ, n ≥ 1 → (X ^ 2 - C (3 * n : ℝ) * X + C (c n) : ℝ[X]).roots = {a n, a (n + 1)}) (h₁ : a 1 = 1) :
    ∀ n ≥ 1, c (2 * n - 1) = 9 * n ^ 2 - 9 * n + 2 ∧ c (2 * n) = 9 * n ^ 2 - 1 := by
  -- By Vieta's formula, show that the sum and product of a_n and a_{n + 1} are 3n and c_n respectively.
  have h₂ (n : ℕ) (hn : n ≥ 1) : a n + a (n + 1) = 3 * n ∧ a n * a (n + 1) = c n := by
    specialize h₀ n hn
    -- Let p(x) = x^2 - 3nx + c_n, then p(x) = 0 has two roots a_n and a_{n + 1}.
    set p : ℝ[X] := X ^ 2 - C (3 * n : ℝ) * X + C (c n) with hp
    have h₂ : p.natDegree = 2 := by
      rw [hp]
      compute_degree!
    have h₃ : p.roots.card = 2 := by
      simp [h₀]
    have h₄ : p.leadingCoeff = 1 := by
      rw [hp, <-Polynomial.coeff_natDegree, h₂]
      simp
    -- Use results of symmetric polynomials.
    have h₅ := Polynomial.coeff_eq_esymm_roots_of_card (h₃ ▸ h₂.symm) (k := 0) (by simp [h₂])
    have h₆ := Polynomial.coeff_eq_esymm_roots_of_card (h₃ ▸ h₂.symm) (k := 1) (by simp [h₂])
    rw [h₂, h₄, h₀, hp] at h₅ h₆
    simp [Multiset.esymm, Multiset.powersetCard_one] at h₅ h₆
    exact ⟨by linarith, h₅.symm⟩
  -- Show that a_{n + 2} = a_n + 3.
  have h₃ (n : ℕ) (hn : n ≥ 1) : a (n + 2) = a n + 3 := by
    have g₀ := (h₂ n hn).1
    have g₁ := (h₂ (n + 1) (by omega)).1
    push_cast at g₁
    linarith
  -- Show that a_2 = 2.
  have h₄ : a 2 = 2 := by
    have := (h₂ 1 (by omega)).1
    simp at this
    linarith
  replace h₁ (n : ℕ) (hn : n ≥ 1) : a (2 * n - 1) = 3 * n - 2 := by
    -- Substitute n by n - 1.
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    induction' n with n hn
    . -- Base case: n = 0.
      norm_num [h₁]
    . -- Inductive case.
      specialize h₃ (2 * (1 + n) - 1) (by omega)
      convert h₃ using 1
      . congr
        omega
      . rw [hn]
        simp
        ring
  replace h₄ (n : ℕ) (hn : n ≥ 1) : a (2 * n) = 3 * n - 1 := by
    -- Substitute n by n - 1.
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    induction' n with n hn
    . -- Base case: n = 0.
      norm_num [h₄]
    . -- Inductive case.
      specialize h₃ (2 * (1 + n)) (by omega)
      convert h₃ using 1
      . rw [hn]
        simp
        ring
  -- Now prove the goal that c_{2n - 1} = 9n^2 - 9n + 2 and c_{2n} = 9n^2 - 1.
  intro n hn
  constructor
  . -- Show that c_{2n - 1} = 9n^2 - 9n + 2 by using the fact that a_{2n - 1} = 3n - 2 and a_{2n} = 3n - 1.
    rw [<-(h₂ (2 * n - 1) (by omega)).2, h₁ n hn, Nat.sub_add_cancel (by omega), h₄ n hn]
    ring
  . -- Show that c_{2n} = 9n^2 - 1 by using the fact that a_{2n} = 3n - 1.
    rw [<-(h₂ (2 * n) (by omega)).2, h₄ n hn, show 2 * n + 1 = 2 * (n + 1) - 1 by omega, h₁ (n + 1) (by omega)]
    push_cast
    ring
