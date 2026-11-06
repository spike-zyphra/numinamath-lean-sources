import Mathlib

open Complex

/- Let $(a_1,b_1),$ $(a_2,b_2),$ $\dots,$ $(a_n,b_n)$ be all the ordered pairs $(a,b)$ of complex numbers with $a^2+b^2\neq 0,$
\[a+\frac{10b}{a^2+b^2}=5, \quad \text{and} \quad b+\frac{10a}{a^2+b^2}=4.\]Find $a_1 + b_1 + a_2 + b_2 + \dots + a_n + b_n.$ -/
theorem algebra_20355 (valid1 valid2 : ℂ → ℂ → Prop)
    (h_valid1 : ∀ a b, valid1 a b = (a + 10 * b / (a ^ 2 + b ^ 2) = 5))
    (h_valid2 : ∀ a b, valid2 a b = (b + 10 * a / (a ^ 2 + b ^ 2) = 4))
    (valid_pairs : Set (ℂ × ℂ))
    (h_valid_pairs : valid_pairs = {p : ℂ × ℂ | p.1 ^ 2 + p.2 ^ 2 ≠ 0 ∧ valid1 p.1 p.2 ∧ valid2 p.1 p.2}) :
    valid_pairs.Finite ∧ ((fin : valid_pairs.Finite) → fin.toFinset.sum (fun p => p.1 + p.2) = 18) := by

  -- lemma, c ≠ 0 → c * a = c * b → a = b
  have l_mul_eq_mul_left {a b c : ℂ} : c ≠ 0 → c * a = c * b → a = b := by
    intro hc h
    apply_fun fun t => t / c at h
    simp [hc] at h
    exact h

  -- lemma, a / b = c / d → (a + c) / (b + d) = a / b
  have l_div_add_eq {a b c d : ℂ} (h1 : b ≠ 0) (h2 : d ≠ 0) (h3 : b + d ≠ 0) : a / b = c / d → (a + c) / (b + d) = a / b := by
    intro h
    set t := a / b
    have ha : a = b * t := (mul_div_cancel₀ a h1).symm
    have hb : c = d * t := by
      apply_fun fun x => d * x at h
      convert h.symm
      field_simp
    rw [ha, hb, ← add_mul, mul_div_cancel_left₀ _ h3]

  -- lemma, a ^ 2 = - b ^ 2 → a = I * b ∨ a = -(I * b)
  have l_sq_eq_neg {a b : ℂ} : a ^ 2 = - b ^ 2 → a = I * b ∨ a = -(I * b) := by
    intro h
    have : a ^ 2 = (I * b) ^ 2 := by rw [mul_pow, I_sq, neg_one_mul, h]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this

  -- the solutions are $(1,2),$ $(4,2),$ $\left( \frac{5}{2}, 2 + \frac{3i}{2} \right),$ $\left( \frac{5}{2}, 2 - \frac{3i}{2} \right)$.
  have (p : (ℂ × ℂ)) : (p.1 ^ 2 + p.2 ^ 2 ≠ 0 ∧ valid1 p.1 p.2 ∧ valid2 p.1 p.2) ↔
    (p = (1, 2) ∨ p = (4, 2) ∨ p = (5/2, 2 + 3 * I / 2) ∨ p = (5/2, 2 - 3 * I / 2)) := by

    obtain ⟨a, b⟩ := p
    constructor

    . dsimp only
      rintro ⟨h, h1, h2⟩
      rw [h_valid1] at h1
      rw [h_valid2] at h2

      -- If $a = 0,$ then $\frac{10}{b} = 5,$ so $b = 2,$ which does not satisfy the second equation.
      have r1 : a = 0 → False := by
        intro h
        norm_num [h] at h1 h2
        norm_num [h2] at h1

      -- If $b = 0,$ then $\frac{10}{a} = 4,$ so $a = \frac{5}{2},$ which does not satisfy the first equation.
      have r2 : b = 0 → False := by
        intro h
        norm_num [h] at h1 h2
        norm_num [h1] at h2

      -- So, we can assume that both $a$ and $b$ are nonzero.
      have h_ab_ne_zero : a ≠ 0 ∧ b ≠ 0 := by
        -- aesop
        subst h_valid_pairs
        simp_all only [eq_iff_iff, ne_eq, mul_eq_mul_left_iff, or_false, implies_true, imp_false, not_false_eq_true,
          and_self]

      -- Then $\frac{5 - a}{b} = \frac{4 - b}{a} = \frac{10}{a^2 + b^2}$.
      have r3 : (5 - a) / b = 10 / (a ^ 2 + b ^ 2) ∧ (4 - b) / a = 10 / (a ^ 2 + b ^ 2) := by
        obtain ⟨h_a_ne_zero, h_b_ne_zero⟩ := h_ab_ne_zero
        constructor
        . apply l_mul_eq_mul_left h_b_ne_zero
          simp [mul_eq_mul_left_iff, h_b_ne_zero]
          apply_fun fun t => (t - a) / b at h1
          convert h1.symm using 1
          ring_nf
          rw [mul_comm b, mul_assoc _ b, ← mul_assoc, mul_inv_cancel_right₀ h_b_ne_zero]
        . apply l_mul_eq_mul_left h_a_ne_zero
          simp [mul_eq_mul_left_iff, h_a_ne_zero]
          apply_fun fun t => (t - b) / a at h2
          convert h2.symm using 1
          ring_nf
          rw [mul_comm a, mul_assoc _ a a⁻¹, ← mul_assoc, mul_inv_cancel_right₀ h_a_ne_zero]

      -- Hence, $\frac{5b - ab}{b^2} = \frac{4a - ab}{a^2} = \frac{10}{a^2 + b^2}$,
      have r4 : (5 * b - a * b) / (b ^ 2) = 10 / (a ^ 2 + b ^ 2) ∧ (4 * a - a * b) / (a ^ 2) = 10 / (a ^ 2 + b ^ 2) := by
        obtain ⟨h_a_ne_zero, h_b_ne_zero⟩ := h_ab_ne_zero
        field_simp
        field_simp at r3
        obtain ⟨t1, t2⟩ := r3
        constructor
        . apply_fun fun t => t * b at t1
          convert t1 using 1 <;> ring
        . apply_fun fun t => t * a at t2
          convert t2 using 1 <;> ring

      -- so $\frac{4a + 5b - 2ab}{a^2 + b^2} = \frac{10}{a^2 + b^2}$,
      have r5 : (4 * a + 5 * b - 2 * a * b) / (a ^ 2 + b ^ 2) = 10 / (a ^ 2 + b ^ 2) := by
        obtain ⟨h_a_ne_zero, h_b_ne_zero⟩ := h_ab_ne_zero
        obtain ⟨t1, t2⟩ := r4
        rw [← t2, show 4 * a + 5 * b - 2 * a * b = (4 * a - a * b) + (5 * b - a * b) by ring]
        apply l_div_add_eq (pow_ne_zero 2 h_a_ne_zero) (pow_ne_zero 2 h_b_ne_zero) h
        rw [t1, t2]

      -- so $4a + 5b - 2ab = 10.$  Then $2ab - 4a - 5b + 10 = 0,$ which factors as $(2a - 5)(b - 2) = 0.$  Hence, $a = \frac{5}{2}$ or $b = 2.$
      have r6 : a = 5 / 2 ∨ b = 2 := by
        apply_fun fun t => t * (a ^ 2 + b ^ 2) at r5
        repeat rw [div_mul_cancel₀ _ h] at r5
        have : (2 * a - 5) * (b - 2) = 0 := by
          rw [sub_mul, mul_sub, mul_sub, show (5:ℂ) * 2 = 10 by norm_num, ← r5]
          ring_nf
        rcases mul_eq_zero.mp this with h | h
        . left
          rw [← eq_of_sub_eq_zero h, mul_div_cancel_left₀ _ two_ne_zero]
        . right
          rw [← eq_of_sub_eq_zero h]

      rcases r6 with ha | hb

      -- If $a = \frac{5}{2},$
      .
        -- then $\frac{5/2}{b} = \frac{10}{\frac{25}{4} + b^2}$.
        norm_num [ha] at r3
        have t1 := r3.left

        -- This simplifies to $4b^2 - 16b + 25 = 0.$
        have : 4 * b ^ 2 - 16 * b + 25 = 0 := by
          norm_num only [ha] at h
          apply (eq_mul_inv_iff_mul_eq₀ h).mp at t1
          field_simp at t1
          apply_fun fun t => t / 5 at t1
          rw [mul_div_cancel_left₀ _ (show (5:ℂ) ≠ 0 by norm_num),
              show (10:ℂ) = 5 * 2 by norm_num, mul_assoc, mul_div_cancel_left₀ _ (show (5:ℂ) ≠ 0 by norm_num)] at t1
          apply_fun fun t => t - 16 * b at t1
          convert t1 using 1 <;> ring

        -- By the quadratic formula, $b = 2 \pm \frac{3i}{2}$.
        have hc1 : (4 : ℂ) ≠ 0 := by norm_num
        have hdiscrim : discrim 4 (-16 : ℂ) 25 = (12 * I) * (12 * I) := by
          dsimp [discrim]
          ring_nf
          rw [I_sq, neg_one_mul]
        have heq : 4 * (b * b) + (-16 : ℂ) * b + 25 = 0 := by
          convert this using 1
          ring_nf
        rcases (quadratic_eq_zero_iff hc1 hdiscrim b).mp heq with hb | hb
        . have : b = 2 + 3 * I / 2 := by
            rw [hb]
            ring_nf
          simp [ha, this]
        . have : b = 2 - 3 * I / 2 := by
            rw [hb]
            ring_nf
          simp [ha, this]


      -- If $b = 2,$
      .
        -- then $\frac{2}{a} = \frac{10}{a^2 + 4}$.
        rw [hb, mul_comm a 2, ← sub_mul, show (4:ℂ) - 2 = 2 by norm_num,
            pow_two a, mul_div_assoc, div_mul_cancel_right₀ h_ab_ne_zero.left, ← div_eq_mul_inv] at r4
        have t1 := r4.right

        -- This simplifies to $a^2 - 5a + 4 = 0,$
        have : a ^ 2 - 5 * a + 4 = 0 := by
          rw [hb, pow_two] at h
          field_simp at t1
          apply_fun fun t => (t / 2 - 5 * a) at t1
          convert t1 using 1 <;> field_simp <;> ring

        -- which factors as $(a - 1)(a - 4) = 0,$
        have : (a - 1) * (a - 4) = 0 := by
          ring_nf
          convert this using 1
          ring_nf

        -- so $a = 1$ or $a = 4.$
        rcases mul_eq_zero.mp this with ha | ha
        <;> simp [eq_of_sub_eq_zero ha, hb]


    -- verify the four pairs
    . intro h
      rw [h_valid1, h_valid2]
      rcases h with h | h | h | h
      -- (a, b) = (1, 2)
      . rw [h]
        dsimp
        norm_num
      -- (a, b) = (4, 2)
      . rw [h]
        dsimp
        norm_num
      -- (a, b) = (5 / 2, 2 + 3 * I / 2)
      . rw [h]
        simp
        ring_nf
        field_simp
        ring_nf
        have t0 : 32 + I * 24 ≠ 0 := by
          by_contra! h_contra
          apply_fun fun t => t.re at h_contra
          norm_num at h_contra
        have t1 : 5 + I * (32 + I * 24)⁻¹ * 120 + (32 + I * 24)⁻¹ * 160 = 10 := by
          suffices h : (32 + I * 24)⁻¹ * (I * 120 + 160) = 10 - 5 from by
            rw [mul_comm I, mul_assoc, add_assoc, ← mul_add]
            exact add_eq_of_eq_sub' h
          rw [show I * 120 + 160 = (32 + I * 24) * 5 by ring]
          field_simp
          norm_num
        have t2 : 4 + I * 3 + (32 + I * 24)⁻¹ * 200 = 8 := by
          have : (32 + I * 24)⁻¹ * 200 = 4 - 3 * I := by
            field_simp
            ring_nf
            rw [I_sq]
            norm_num
          rw [this]
          ring
        exact ⟨t0, t1, t2⟩
      -- (a, b) = (5 / 2, 2 - 3 * I / 2)
      . rw [h]
        simp
        ring_nf
        field_simp
        ring_nf
        have t0 : 32 - I * 24 ≠ 0 := by
          by_contra! h_contra
          apply_fun fun t => t.re at h_contra
          norm_num at h_contra
        have t1 : 5 - I * (32 - I * 24)⁻¹ * 120 + (32 - I * 24)⁻¹ * 160 = 10 := by
          suffices h : (32 - I * 24)⁻¹ * (160 - I * 120) = 10 - 5 from by
            rw [mul_comm I, mul_assoc, sub_add_comm, ← mul_sub]
            exact add_eq_of_eq_sub h
          rw [show 160 - I * 120 = (32 - I * 24) * 5 by ring]
          field_simp
          norm_num
        have t2 : 4 - I * 3 + (32 - I * 24)⁻¹ * 200 = 8 := by
          have : (32 - I * 24)⁻¹ * 200 = 4 + 3 * I := by
            field_simp
            ring_nf
            rw [I_sq]
            norm_num
          rw [this]
          ring
        exact ⟨t0, t1, t2⟩

  have : valid_pairs = {(1, 2), (4, 2), (5/2, 2 + 3 * I / 2), (5/2, 2 - 3 * I / 2)} := by
    simp only [h_valid_pairs, ne_eq, this]
    rfl

  constructor
  . rw [this]
    apply Set.toFinite
  . intro h
    simp only [this, Set.toFinite_toFinset, Set.toFinset_insert, Set.toFinset_singleton]
    repeat rw [Finset.sum_insert]
    rw [Finset.sum_singleton]
    . dsimp
      ring_nf
    . simp
      by_contra!
      apply_fun fun t => (t - 2) * 2 / 3 at this
      ring_nf at this
      have : I ≠ -I := by
        by_contra h
        apply CharZero.eq_neg_self_iff.mp at h
        exact I_ne_zero h
      contradiction
    . simp
      have : ¬ (4:ℂ) = 5 / 2 := by norm_num
      exact fun a _ => this a
    . simp
      have : ¬ (1:ℂ) = 5 / 2 := by norm_num
      exact fun a _ => this a
