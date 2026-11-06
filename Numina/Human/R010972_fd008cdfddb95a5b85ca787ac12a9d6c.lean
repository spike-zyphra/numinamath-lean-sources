import Mathlib
open Nat Real Finset Set
noncomputable section

/-Evdokimov M.A.
Tanya took a list of one hundred numbers $1,2,3, \ldots, 100$ and crossed out several of them. It turned out that no matter which two numbers from the remaining ones Tanya took as $\$ a \$$ and $\$ b \$$, the equation $\$ x \wedge 2+a x+b=0 \$$ has at least one real root. What is the maximum number of numbers that could remain uncrossed?-/
theorem algebra_200004 :
  ∃ S : Finset ℕ, (S ⊆ Icc 1 100) ∧
    (∀ a ∈ S, ∀ b ∈ S, ∃ x : ℝ, x ^ 2 + (a : ℝ) * x + (b : ℝ) = 0) ∧
    S.card = 81 := by
  -- Construct the subset $S = {20, 21, ..., 100}$.
  let S : Finset ℕ := Icc 20 100
  use S
  -- Prove three subgoals: $S ⊆ Icc 1 100$, the equation has real roots, $S.card = 81$.
  constructor
  -- Subgoal : $S ⊆ Icc 1 100$.
  have h_subset : S ⊆ Icc 1 100 := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨le_trans (by norm_num) hn.1, hn.2⟩
  exact h_subset
  constructor
  -- Subgoal: For any $a, b ∈ S$, the equation $x^2 + a x + b = 0$ has real roots.
  have h_roots : ∀ a ∈ S, ∀ b ∈ S, ∃ x : ℝ, x ^ 2 + (a : ℝ) * x + (b : ℝ) = 0 := by
    intros a ha b hb
    -- The equation has real roots if and only if the discriminant $a^2 - 4b ≥ 0$.
    suffices discr_nonneg : (a : ℝ) ^ 2 - 4 * (b : ℝ) ≥ 0 by
      let discr := (a : ℝ) ^ 2 - 4 * (b : ℝ)
      have h_quadratic : ∀ x : ℝ, x ^ 2 + (a : ℝ) * x + (b : ℝ) = (x + (a : ℝ) / 2) ^ 2 - discr / 4 := by
        intro x
        ring_nf
      have h_discr_nonneg : discr / 4 ≥ 0 := by
        have : discr / 4 = ((a : ℝ) ^ 2 - 4 * (b : ℝ)) / 4 := by rfl
        rw [this]
        linarith [discr_nonneg]
      let x₀ := Real.sqrt (discr / 4)
      have hx₀ : x₀ ^ 2 = discr / 4 := by
        unfold x₀
        have h_sqrt_eq : Real.sqrt ((discr / 4) ^ 2) = (Real.sqrt (discr / 4)) ^ 2 := by
            rw [Real.sqrt_sq h_discr_nonneg]
            rw [Real.sq_sqrt h_discr_nonneg]
        rw [← h_sqrt_eq]
        exact Real.sqrt_sq h_discr_nonneg
      use (- (a : ℝ) / 2 + x₀)
      rw [h_quadratic]
      have h_simplify : (- (a : ℝ) / 2 + x₀ + (a : ℝ) / 2) = x₀ := by ring
      rw [h_simplify]
      rw [← hx₀]
      rw [sub_self]
    -- Prove the discriminant is non-negative.
    have h_a : (a : ℝ) ≥ 20 := by
      rw [Finset.mem_Icc] at ha
      exact Nat.cast_le.mpr ha.1
    have h_b : (b : ℝ) ≤ 100 := by
      rw [Finset.mem_Icc] at hb
      exact Nat.cast_le.mpr hb.2
    have h_a_sq : (a : ℝ) ^ 2 ≥ 400 := by
      have h_a_pos : (a : ℝ) ≥ 0 := le_trans (by norm_num) h_a
      have h_a_ge_20 : (a : ℝ) ≥ (20 : ℝ) := h_a
      have h_sq_mono : (20 : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 := by nlinarith
      rw [← Nat.cast_pow]
      exact_mod_cast h_sq_mono
    have h_4b : 4 * (b : ℝ) ≤ 400 := by
      have h_b_nonneg : (b : ℝ) ≥ 0 := by
        rw [Finset.mem_Icc] at hb
        exact Nat.cast_nonneg b
      have h_4b_le : 4 * (b : ℝ) ≤ 4 * (100 : ℝ) := mul_le_mul_of_nonneg_left h_b (by norm_num)
      exact_mod_cast h_4b_le
    show (a : ℝ) ^ 2 - 4 * (b : ℝ) ≥ 0
    calc
      (a : ℝ) ^ 2 - 4 * (b : ℝ) ≥ 400 - 4 * (b : ℝ) := sub_le_sub_right h_a_sq _
      _ ≥ 400 - 400 := sub_le_sub_left h_4b 400
      _ = 0 := by norm_num
  exact h_roots
  -- Subgoal : $S.card = 81$.
  have h_card : S.card = 81 := by
    rw [card_Icc]
  exact h_card
