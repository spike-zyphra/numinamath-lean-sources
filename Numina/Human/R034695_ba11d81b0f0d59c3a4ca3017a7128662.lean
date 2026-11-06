import Mathlib
open Finset
/- One, (40 points) Given that $A$ is a finite set of positive real numbers, and for any positive number $a$, the sets $\{x \in A \mid x>a\}$ and $\left\{x \in A \left\lvert\, x<\frac{1}{a}\right.\right\}$ have the same parity in the number of elements. Prove: $\prod_{x \in A} x=1$.

 -/
theorem number_theory_127343 (A : Finset ℝ) (hpos : ∀ x ∈ A, x > 0)
    (h : ∀ a > 0, #{x ∈ A | x > a} ≡ #{x ∈ A | x < 1 / a} [MOD 2]) :
    ∏ x ∈ A, x = 1 := by
  -- we show that the function x => 1/x is an involution
  apply prod_involution (fun x hx => 1 / x)
  · exact fun x hA => mul_one_div_cancel (hpos x hA).ne.symm
  · intro x hA hx heq
    have := calc x * x = x * (1 / x) := by rw [heq]
      _ = 1 := by exact mul_one_div_cancel (hpos x hA).ne.symm
    rcases mul_self_eq_one_iff.mp this with hxeq | hxeq
    contradiction
    linarith [hpos x hA]
  · exact fun x hA => one_div_one_div x
  -- show b ∈ A → 1/b ∈ A
  · intro b hA
    -- A is the disjoint union of sets where x < c, x = c, x > c
    have card_A_decomp : ∀ c, #{x ∈ A | x ≤ c} + #{x ∈ A | x > c} = #A
    · intro c; conv_lhs => arg 2; arg 1; arg 1; intro x; rw [gt_iff_lt, ←not_le]
      apply filter_card_add_filter_neg_card_eq_card
    have le_split : ∀ c, {x ∈ A | x ≤ c} = {x ∈ A | x < c} ∪ {x ∈ A | x = c}
    · intro c; ext x; simp; rw [←and_or_left, and_congr_right_iff]
      exact fun hA => le_iff_lt_or_eq
    have le_card : ∀ c, #{x ∈ A | x ≤ c} = #{x ∈ A | x < c} + #{x ∈ A | x = c}
    · intro c; conv_lhs => rw [le_split]
      apply card_union_of_disjoint
      exact disjoint_filter.mpr fun x hxA hx => ne_of_lt hx
    conv at card_A_decomp => intro c; rw [le_card]
    -- take the above equation mod 2,
    -- rewrite using the mod condition given with values b and (1/b)
    have hb : #({x ∈ A | x = b}) ≡ #({x ∈ A | x = 1 / b}) [MOD 2]
    · apply Nat.ModEq.add_left_cancel (h b (hpos b hA)) _
      apply Nat.ModEq.add_right_cancel (h (1 / b) (one_div_pos.mpr (hpos b hA))).symm _
      rw [one_div_one_div b, add_comm, add_comm #({x ∈ A | x > b}) _, ←add_assoc, card_A_decomp b, card_A_decomp (1/b)]
    -- this is exactly the statement that b ∈ A ↔ 1/b ∈ A
    simp only [hA, filter_eq', ↓reduceIte, card_singleton] at hb
    split_ifs at hb with hgoal; exact hgoal; contradiction