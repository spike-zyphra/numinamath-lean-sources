import Mathlib
set_option linter.unusedVariables false

-- Lemma for the transformation of product and factorial.
lemma prod_Icc_id_eq_factorial : ∀ n : ℕ, (∏ x ∈ Finset.Icc 1 n, x) = Nat.factorial n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_Icc_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Icc_id_eq_factorial n, mul_comm]

/-Soit $n \geqslant 1$ un entier. Pour tout sous-ensemble non vide $A$ de $\{1,2, \ldots, n\}$, on note $P(A)$ le produit de tous les éléments de $A$. Par exemple, pour $A=\{2,4,7\}$, on a $P(A)=$ 56. Déterminer la somme des $\frac{1}{P(A)}$ lorsque $A$ parcourt tous les sous-ensembles non vides de $\{1,2, \ldots, n\}$.-/
theorem combinatorics_605441 {n : ℕ} (hn : 1 ≤ n) :
    ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (1 / (∏ x ∈ A, x) : ℚ) = n := by
  -- Introduce the polynomial identity.
  have h_poly_identity : ∏ i ∈ Finset.Icc 1 n, (1 + (1 / i : ℚ)) =
    ∑ A ∈ (Finset.Icc 1 n).powerset, (∏ x ∈ A, (1 / x : ℚ)) := by
    rw [Finset.prod_one_add (Finset.Icc 1 n)]

  -- Separate the empty subset term.
  have h_substitute : ∑ A ∈ (Finset.Icc 1 n).powerset, (∏ x ∈ A, (1 / x : ℚ)) =
    1 + ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (∏ x ∈ A, (1 / x : ℚ)) := by
    let f : Finset ℕ → ℚ := fun A => ∏ x ∈ A, (1 / x : ℚ)
    have h_empty : f ∅ = 1 := Finset.prod_empty
    have h_empty_mem : ∅ ∈ (Finset.Icc 1 n).powerset := Finset.empty_mem_powerset (Finset.Icc 1 n)
    rw [← Finset.sum_erase_add (s := (Finset.Icc 1 n).powerset) (f := f) (a := ∅) h_empty_mem]
    rw [Finset.erase_eq, h_empty, add_comm]

  -- Compute the left-hand side.
  have h_left_side : ∏ i ∈ Finset.Icc 1 n, (1 + (1 / i : ℚ)) = (n + 1 : ℚ) := by
    calc
      ∏ i ∈ Finset.Icc 1 n, (1 + (1 / i : ℚ))
      = ∏ i ∈ Finset.Icc 1 n, ((i + 1) / i : ℚ) := by
        apply Finset.prod_congr rfl
        intro i h_i
        have : i ≠ 0 := by
          have : 1 ≤ i := (Finset.mem_Icc.mp h_i).1
          nlinarith
        field_simp
      _ = (∏ i ∈ Finset.Icc 1 n, (i + 1 : ℚ)) / (∏ i ∈ Finset.Icc 1 n, i) := by
        rw [Finset.prod_div_distrib]
        simp
      _ = (Nat.factorial n) * (n + 1) / Nat.factorial n := by
        have h_num : ∏ i ∈ Finset.Icc 1 n, (i + 1 : ℚ) = ((∏ i ∈ Finset.Icc 1 n, i) * (n + 1) : ℚ) := by 
          have h₂ : ∀ (n : ℕ), ∏ i ∈ Finset.Icc 1 n, (i + 1 : ℚ) = ((∏ i ∈ Finset.Icc 1 n, i) * (n + 1) : ℚ) := by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              rw [Finset.prod_Icc_succ_top (by norm_num : 1 ≤ n.succ), ih]
              simp [Finset.prod_Icc_succ_top, Nat.factorial_succ, mul_add, add_mul, Nat.cast_add, Nat.cast_one, mul_one, Nat.cast_mul]
          have h₃ := h₂ n
          exact h₃
        rw [prod_Icc_id_eq_factorial n] at h_num
        rw [prod_Icc_id_eq_factorial n, h_num]
      _ = (n + 1 : ℚ) := by
        field_simp

  -- Combine the identity.
  have h_sum_with_empty : 1 + ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (∏ x ∈ A, (1 / x : ℚ)) = (n + 1 : ℚ) := by
    rw [← h_substitute, ← h_poly_identity, h_left_side]

  -- Derive the target sum.
  have h_final_sum : ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (1 / (∏ x ∈ A, x) : ℚ) = (n : ℚ) := by
    calc
    ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (1 / (∏ x ∈ A, x) : ℚ)
    = ∑ A ∈ (Finset.Icc 1 n).powerset \ {∅}, (∏ x ∈ A, (1 / x : ℚ)) := by
      apply Finset.sum_congr rfl
      intro A hA
      simp
    _ = (n : ℚ) := by linarith

  exact h_final_sum
