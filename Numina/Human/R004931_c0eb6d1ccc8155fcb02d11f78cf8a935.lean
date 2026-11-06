import Mathlib

open Set
open scoped Finset

/- Soit $n \geqslant 1$ un entier. Déterminer tous les entiers $p \geqslant 1$ pour lesquels il existe des entiers strictement positifs $x_{1} < x_{2} < \cdots < x_{n}$ tels que
  $$ \frac{1}{x_{1}}+\frac{2}{x_{2}}+\cdots+\frac{n}{x_{n}}=p $$ -/
theorem algebra_604684 (n : ℕ) :
    {p : ℕ | p ≥ 1 ∧
     ∃ x : Icc 1 n → ℕ, (∀ i, 0 < x i) ∧ StrictMono x ∧
     ∑ i : Icc 1 n, (i : ℝ) / x i = p} = Icc 1 n := by
  -- Fix a positive integer `p` and prove that the conditions on the both sides
  -- are equivalent.
  ext p
  simp only [ge_iff_le, mem_Icc, mem_setOf_eq, and_congr_right_iff]
  refine fun hp => ⟨fun | ⟨x, x_pos, mono_x, sum_x⟩ => ?_, fun hp' => ?_⟩
  · -- Given that $\frac{1}{x_1} + \cdots + \frac{n}{x_n} = p$, we prove that $p \leq n$.
    rify
    rw [← sum_x]
    clear sum_x
    -- We prove that $i \leq x_i$ by induction.
    have i_le_x_i (i : Icc 1 n) : i ≤ x i := by
      cases' i with i hi
      have hi' := hi.1
      induction i, hi' using Nat.le_induction with
      | base =>
        -- Firstly we have $1 \leq x_1$.
        exact Nat.add_one_le_of_lt (x_pos _)
      | succ i one_le ih =>
        -- If $i \leq x_i$, we have $i \leq x_i < x_{i + 1}$, so $i + 1 \leq x_{i + 1}$.
        refine Nat.add_one_le_of_lt (lt_of_le_of_lt (ih ?_) ?_)
        · rw [mem_Icc] at hi ⊢
          omega
        · apply mono_x
          simp
    -- Then, $\frac{1}{x_1} + \cdots + \frac{n}{x_n} \leq \frac{1}{1} + \cdots +
    -- \frac{n}{n} = n$, so $p < n$.
    calc
      _ ≤ ∑ i : Icc 1 n, (i : ℝ) / i := by
        apply Finset.sum_le_sum
        rintro i -
        -- From $i \leq x_i$ we can prove that $\frac{i}{x_i} \leq \frac{i}{i}$.
        rw [div_le_div_iff_of_pos_left
          (by norm_cast; linarith [i.2.1])
          (by norm_cast; apply x_pos)
          (by norm_cast; linarith [i.2.1])]
        norm_cast
        apply i_le_x_i
      _ = _ := by
        -- Use `conv` tactic to rewrite under binders.
        conv =>
          enter [1, 2, i]
          rw [div_self (by norm_cast; linarith [i.2.1])]
        simp
  · -- Given an integer $1 \leq p \leq n$, we construct a sequence $x_i$ satisfies the condition.
    let x (i : Icc 1 n) : ℕ := if i < p then i else i * (n - p + 1)
    refine ⟨x, ?_, ?_, ?_⟩
    · -- The sequence $x_i$ is positive. It is trivial since $0 < i$ and $0 < n - p + 1$.
      simp only [Subtype.forall, mem_Icc, and_imp, x]
      intros
      positivity
    · -- The sequence $x_i$ is strictly monotone.
      intro ⟨i, i_ge, i_le⟩ ⟨j, j_ge, j_le⟩ lt
      simp only [Subtype.mk_lt_mk, x] at lt ⊢
      -- The `split_ifs` tactic splits the original goal into 4 subgoals
      -- based on the truth values of the conditions `i < p` and `j < p`.
      -- Three of them can be solved by some simple methods, such as applying
      -- theorem `Nat.mul_lt_mul_of_pos_right` and `omega` tactic.
      split_ifs with hi hj <;> (
        try apply Nat.mul_lt_mul_of_pos_right
        repeat omega
      )
      -- It remains a hard goal. Given that `i < p` and `j ≥ p`, we prove that
      -- `i < j * (n - p + 1)`. We can prove it by `i < j` and `1 ≤ n - p + 1`.
      calc
        _ < j * 1 := by simpa
        _ ≤ _ := by
          apply Nat.mul_le_mul_left
          omega
    · -- Move the `if ... then ... else ...` structure to the outermost level,
      -- and split the summation using `Finset.sum_ite`.
      simp only [x]
      push_cast
      simp only [div_ite, Finset.sum_ite]
      -- Rewrite $\frac{x}{x}$ and $\frac{x}{x (n - p + 1)}$ to $1$ and $\frac{1}{n - p + 1}$.
      -- We use the `conv` tactic to rewrite under binders.
      conv =>
        enter [1, 1, 2, i]
        rw [div_self (by norm_cast; linarith [i.2.1])]
      conv =>
        enter [1, 2, 2, i]
        rw [div_mul_cancel_left₀ (by norm_cast; linarith [i.2.1])]
      -- The cardinality of a subset of `Icc 1 n` is equal to the cardinality of the
      -- lifted subset of `ℕ`, since the lift map `Subtype.val : Icc 1 n → ℕ` is injective.
      simp [← Finset.card_image_of_injective _ (Subtype.val_injective)]
      norm_cast
      -- Rephrase the goal. We can easily prove the lifted sets are exactly `Finset.Ico 1 p`
      -- and `Finset.Icc p n`, both are finite subsets of `ℕ`. So we can compute their
      -- cardinality by `simp`.
      convert_to #(.Ico 1 p) + #(.Icc p n) * ((n + 1 - p : ℕ) : ℝ)⁻¹ = p using 5
      · ext i; simp; omega
      · ext i; simp; omega
      · omega
      · simp only [Nat.card_Ico, Nat.card_Icc]
        -- Split the expressions like `↑(a - b)` using `Nat.cast_sub`.
        rw [mul_inv_cancel₀, Nat.cast_sub (by omega)]
        · norm_cast; omega
        · norm_cast; omega
