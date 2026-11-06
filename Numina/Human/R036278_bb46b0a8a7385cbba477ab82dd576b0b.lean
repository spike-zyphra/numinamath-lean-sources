import Mathlib
open Polynomial

/- The sequence $\left\{ {{a}_{n}} \right\}$ satisfies: ${{a}_{1}}=1$, and for each $n\in {{\mathbf{N}}^{*}}$, ${{a}_{n}}$ and ${{a}_{n+1}}$ are the roots of the equation ${{x}^{2}}+3nx+{{b}_{n}}=0$. Then $\sum\limits_{k=1}^{20}{{{b}_{k}}}=$__ __.-/
theorem algebra_621237 {a b : ℕ → ℝ}
    (h₀ : ∀ n : ℕ, n ≥ 1 → (X ^ 2 + C (3 * n : ℝ) * X + C (b n) : ℝ[X]).roots = {a n, a (n + 1)}) (h₁ : a 1 = 1) :
    ∑ k ∈ Finset.Icc 1 20, b k = 6385 := by
  -- By Vieta's formula, show that the sum and product of a_n and a_{n + 1} are -3n and b_n respectively.
  have h₂ (n : ℕ) (hn : n ≥ 1) : a n + a (n + 1) = -3 * n ∧ a n * a (n + 1) = b n := by
    specialize h₀ n hn
    -- Let p(x) = x^2 + 3nx + b_n, then p(x) = 0 has two roots a_n and a_{n + 1}.
    set p : ℝ[X] := X ^ 2 + C (3 * n : ℝ) * X + C (b n) with hp
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
    constructor
    <;> linarith
  -- Show that {a_n + 3n / 2 - 3 / 4} is a geometric sequence of ratio -1.
  have h₃ (n : ℕ) (hn : n ≥ 1) : a (n + 1) + 3 * (n + 1) / 2 - 3 / 4 = -(a n + 3 * n / 2 - 3 / 4) := by
    specialize h₂ n hn
    linarith
  -- Show that a_n + 3n / 2 - 3 / 4 = (-1) ^ (n - 1) * (7 / 4).
  have h₄ (n : ℕ) (hn : n ≥ 1) : a n + 3 * n / 2 - 3 / 4 = (-1) ^ (n - 1) * (7 / 4) := by
    -- Substitute n by n - 1.
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    clear hn
    induction' n with n hn
    . -- Base case: n = 0.
      norm_num [h₁]
    . -- Inductive case.
      specialize h₃ (n + 1) (by omega)
      convert h₃ using 1
      . congrm a ?_ + ?_ - 3 / 4
        . ac_rfl
        . simp
      . rw [hn]
        simp
        ring
  -- Compute the sum easily.
  calc
    ∑ k ∈ Finset.Icc 1 20, b k = ∑ k ∈ Finset.Icc 1 20, ((-1 : ℝ) ^ (k - 1) * (7 / 4) - 3 * (k : ℕ) / 2 + 3 / 4) * ((-1) ^ ((k + 1) - 1) * (7 / 4) - 3 * (k + 1) / 2 + 3 / 4) := by
      rw [Finset.sum_congr]
      . rfl
      . intro n hn
        simp at hn
        rw [<-h₄ n hn.1, <-h₄ (n + 1) (by omega), <-(h₂ n hn.1).2]
        congrm ?_ * ?_
        . ring
        . push_cast
          ring
    _ = 6385 := by
      norm_num [Finset.sum_Icc_succ_top]
  