import Mathlib
open Real Finset Set Nat List
noncomputable section

-- Lemma $1$: Addition of rational numbers preserves rationality.
lemma rational_add {x y : ℝ} (hx : x ∈ range Rat.cast) (hy : y ∈ range Rat.cast) :
    x + y ∈ range Rat.cast := by
  obtain ⟨qx, hqx⟩ := hx
  obtain ⟨qy, hqy⟩ := hy
  use qx + qy
  have h_sum : x + y = Rat.cast qx + Rat.cast qy := by
    rw [hqx, hqy]
  rw [h_sum, Rat.cast_add]

-- Lemma $2$: Subtraction of rational numbers preserves rationality.
lemma rational_sub {x y : ℝ} (hx : x ∈ range Rat.cast) (hy : y ∈ range Rat.cast) :
    x - y ∈ range Rat.cast := by
  obtain ⟨qx, hqx⟩ := hx
  obtain ⟨qy, hqy⟩ := hy
  use qx - qy
  have h_sum : x - y = Rat.cast qx - Rat.cast qy := by
    rw [hqx, hqy]
  rw [h_sum, Rat.cast_sub]

/-4. Several different numbers are written on the blackboard, such that the sum of any three of them is a rational number, while the sum of any two is an irrational number. The maximum number of numbers that can be written on the blackboard is $\qquad$-/
theorem number_theory_608888 :
  IsGreatest {n | ∃ S : Finset ℝ,
    S.card = n ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Irrational (x + y)) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y ∧ y ≠ z ∧ x ≠ z → x + y + z ∈ range Rat.cast)} 3 := by
  let valid_card := {n | ∃ S : Finset ℝ,
    S.card = n ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Irrational (x + y)) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y ∧ y ≠ z ∧ x ≠ z → x + y + z ∈ range Rat.cast)}
  constructor
  -- Part $1$: Prove that $3$ is in the set of valid cardinalities.
  · use {Real.sqrt 2, 2 * Real.sqrt 2, -3 * Real.sqrt 2}
    constructor
    -- Prove the set has exactly $3$ elements
    · simp [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
      have h_neq_1 : Real.sqrt 2 ≠ 2 * Real.sqrt 2 := by norm_num
      have h_neq_2 : Real.sqrt 2 ≠ -3 * Real.sqrt 2 := by
        intro h
        have h' : 1 * √2 = -3 * √2 := by rw [one_mul];exact h
        have : (1 : ℝ) = -3 := by
          have : √2 ≠ 0 := by norm_num
          exact (mul_left_inj' this).mp h'
        linarith
      have h_neq_3 : 2 * Real.sqrt 2 ≠ -3 * Real.sqrt 2 := by
        intro h
        have : (2 : ℝ) = -3 := by
          have : √2 ≠ 0 := by norm_num
          exact (mul_left_inj' this).mp h
        linarith
      have h_card : #{√2, 2 * √2, -3 * Real.sqrt 2} = 3 := by
        apply Finset.card_eq_three.mpr
        use √2, 2 * √2, -3 * Real.sqrt 2
      have : -(3 * √2) = -3 * √2 := by ring
      rw [← this] at h_card
      exact h_card
    constructor
    -- Prove that any two distinct elements sum to an irrational number.
    · intros x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx hy
      have h_sum : x + y = 3 * Real.sqrt 2 ∨ x + y = -2 * Real.sqrt 2 ∨ x + y = -Real.sqrt 2 := by
        rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
        · contradiction
        · left; ring
        · right; left; ring
        · left; ring
        · contradiction
        · right; right; ring
        · right; left; ring
        · right; right; ring
        · contradiction
      rcases h_sum with (h | h | h)
      · rw [h, mul_comm];exact Irrational.mul_rat irrational_sqrt_two (by norm_num : (3 : ℚ) ≠ 0)
      · have h₁: Irrational (√2 * 2):= by
          exact Irrational.mul_rat irrational_sqrt_two (by norm_num : (2 : ℚ) ≠ 0)
        have h₂: √2 * -2 = -(√2 * 2) := by ring
        rw [h, mul_comm, h₂];exact irrational_neg_iff.mpr h₁
      · have h₁: Irrational (√2 * 1):= by
          rw [mul_one]
          exact irrational_sqrt_two
        have h₂: -√2 = -(√2 * 1) := by norm_num
        rw [h, h₂];exact irrational_neg_iff.mpr h₁
    · intros x hx y hy z hz hxyz
      simp [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
      -- Prove that the sum $x + y + z$ equals $√2 + 2√2 - 3√2$.
      have h_sum_eq : x + y + z = Real.sqrt 2 + 2 * Real.sqrt 2 + (-3 * Real.sqrt 2) := by
        rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl) <;> rcases hz with (rfl | rfl | rfl) <;> simp_all [add_assoc, add_left_comm, add_comm]
      have h_eq_zero : Real.sqrt 2 + 2 * Real.sqrt 2 + (-3 * Real.sqrt 2) = 0 := by ring
      rw [h_eq_zero] at h_sum_eq
      use 0
      simp [← add_mul]
      exact h_sum_eq.symm
  -- Part $2$: Prove that any valid cardinality is at most $3$.
  · intros n hn
    obtain ⟨S, hS_card, h_two_irrational, h_three_rational⟩ := hn
    by_contra h_n_gt_3
    have h_card_ge_4 : S.card ≥ 4 := by omega
    -- Select four distinct elements $a, b, c, d$.
    have h_exists_abcd : ∃ a b c d : ℝ, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
      have h_T1_nonempty : S.Nonempty := by
        apply Finset.card_ne_zero.mp
        nlinarith
      obtain ⟨a, ha⟩ := h_T1_nonempty
      let T2 := S.erase a
      have T2_card: T2.card ≥ 3 := by
        rw [Finset.card_erase_of_mem ha]
        omega
      have h_T2_nonempty : T2.Nonempty := by
        apply Finset.card_ne_zero.mp
        nlinarith
      obtain ⟨b, hb⟩ := h_T2_nonempty
      let T3 := T2.erase b
      have T3_card: T3.card ≥ 2 := by
        rw [Finset.card_erase_of_mem hb]
        omega
      have h_T3_nonempty : T3.Nonempty := by
        apply Finset.card_ne_zero.mp
        nlinarith
      obtain ⟨c, hc⟩ := h_T3_nonempty
      let T4 := T3.erase c
      have T4_card: T4.card ≥ 1 := by
        rw [Finset.card_erase_of_mem hc]
        omega
      have h_T4_nonempty : T4.Nonempty := by
        apply Finset.card_ne_zero.mp
        nlinarith
      obtain ⟨d, hd⟩ := h_T4_nonempty
      have h_b : b ≠ a ∧ b ∈ S := by rwa [Finset.mem_erase] at hb
      have h_c : c ≠ a ∧ c ≠ b ∧ c ∈ S := by
        rw [Finset.mem_erase, Finset.mem_erase] at hc
        exact ⟨hc.2.1, hc.1,hc.2.2⟩
      have h_d : d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ d ∈ S := by
        rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at hd
        exact ⟨hd.2.2.1, hd.2.1, hd.1, hd.2.2.2⟩
      exact ⟨a, b, c, d, ha, h_b.2, h_c.2.2, h_d.2.2.2, h_b.1.symm, h_c.1.symm, h_d.1.symm, h_c.2.1.symm, h_d.2.1.symm, h_d.2.2.1.symm⟩
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := h_exists_abcd
    -- Prove that $a + b + c$ and $b + c + d$ are rational.
    have h_abc_rational : a + b + c ∈ range Rat.cast := by
      apply h_three_rational a ha b hb c hc
      exact ⟨hab, hbc, hac⟩
    have h_bcd_rational : b + c + d ∈ range Rat.cast := by
      apply h_three_rational b hb c hc d hd
      exact ⟨hbc, hcd, hbd⟩
    -- Prove that $d - a$ is rational.
    have h_d_minus_a_rational : d - a ∈ range Rat.cast := by
      have h_diff : d - a = (b + c + d) - (a + b + c) := by ring
      rw [h_diff]
      exact rational_sub h_bcd_rational h_abc_rational
    -- Prove that $b - a$ is rational.
    have h_b_minus_a_rational : b - a ∈ range Rat.cast := by
      have h_b_minus_a : b - a = (b + c + d) - (a + c + d) := by ring
      have h_acd_rational : a + c + d ∈ range Rat.cast := by
        apply h_three_rational a ha c hc d hd
        exact ⟨hac, hcd, had⟩
      have h_bcd_rational : b + c + d ∈ range Rat.cast := h_bcd_rational
      rw [h_b_minus_a]
      exact rational_sub h_bcd_rational h_acd_rational
    -- Prove that $c - a$ is rational.
    have h_c_minus_a_rational : c - a ∈ range Rat.cast := by
      have h_c_minus_a : c - a = (b + c + d) - (a + b + d) := by ring
      have h_abd_rational : a + b + d ∈ range Rat.cast := by
        apply h_three_rational a ha b hb d hd
        exact ⟨hab, hbd, had⟩
      have h_bcd_rational : b + c + d ∈ range Rat.cast := h_bcd_rational
      rw [h_c_minus_a]
      exact rational_sub h_bcd_rational h_abd_rational
    -- Express $b = a + r₁$, $c = a + r₂$, $d = a + r₃$.
    have h_b_form : ∃ r₁ : ℚ, b = a + r₁ := by
      obtain ⟨r₁, hr₁⟩ := h_b_minus_a_rational
      use r₁
      linarith
    have h_c_form : ∃ r₂ : ℚ, c = a + r₂ := by
      obtain ⟨r₂, hr₂⟩ := h_c_minus_a_rational
      use r₂
      linarith
    have h_d_form : ∃ r₃ : ℚ, d = a + r₃ := by
      obtain ⟨r₃, hr₃⟩ := h_d_minus_a_rational
      use r₃
      linarith
    obtain ⟨r₁, hr₁⟩ := h_b_form
    obtain ⟨r₂, hr₂⟩ := h_c_form
    obtain ⟨r₃, hr₃⟩ := h_d_form
    -- Prove that $a$ is rational.
    have h_a_rational : a ∈ range Rat.cast := by
      have h_abc_form : a + b + c = 3 * a + r₁ + r₂ := by
        rw [hr₁, hr₂]
        ring
      have h_abc_rat : 3 * a + r₁ + r₂ ∈ range Rat.cast := by
        rw [← h_abc_form]
        exact h_abc_rational
      have h_r₁_r₂_rat : (r₁ + r₂ : ℝ) ∈ range Rat.cast := by
        use r₁ + r₂
        simp [Rat.cast_add]
      obtain ⟨q, hq⟩ := h_abc_rat
      obtain ⟨q_r, hq_r⟩ := h_r₁_r₂_rat
      use (q - q_r) / 3
      have h_eq : 3 * a + r₁ + r₂ = 3 * a + (r₁ + r₂) := by ring
      rw [← hq, ← hq_r] at h_eq
      field_simp
      linarith
    -- Derive a contradiction: $a + b$ is rational.
    have h_contradiction : False := by
      have h_a_b_rational : a + b ∈ range Rat.cast := by
        rw [hr₁, ← add_assoc]
        have h_a_a_rat : a + a ∈ range Rat.cast := rational_add h_a_rational h_a_rational
        have h_r₁_rat : (Rat.cast r₁ : ℝ) ∈ range Rat.cast := by
          use r₁
        exact rational_add h_a_a_rat h_r₁_rat
      have h_a_b_irrational : Irrational (a + b) := h_two_irrational a ha b hb hab
      have h_not_rat : a + b ∉ range Rat.cast := h_a_b_irrational
      contradiction
    contradiction
