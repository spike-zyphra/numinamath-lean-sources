import Mathlib


set_option maxHeartbeats 400000
/-
Let S = {2, 3, 4, ...} denote the set of integers that are greater than or equal to 2.
Does there exist a function f: S → S such that
f(a) * f(b) = f(a^2 * b^2)
for all a, b ∈ S with a ≠ b?

We represent S implicitly by working with Nat (ℕ) and adding hypotheses `n ≥ 2`.
The function f will have type ℕ → ℕ.
The property f: S → S means ∀ n ≥ 2, f n ≥ 2.
-/

-- Define the property the function must satisfy
structure FuncProp (f : ℕ → ℕ) : Prop where
  codomain_ge_2 : ∀ n, n ≥ 2 → f n ≥ 2
  functional_eq : ∀ a b, a ≥ 2 → b ≥ 2 → a ≠ b → f a * f b = f (a ^ 2 * b ^ 2)

-- The main theorem: No such function exists
theorem Algebra_605623 : ¬ (∃ f : ℕ → ℕ, FuncProp f) := by
  -- Proof by contradiction: Assume such a function f exists
  intro h_exists
  obtain ⟨f, hf⟩ := h_exists

  -- Unpack the properties of f
  have h_codom : ∀ n, n ≥ 2 → f n ≥ 2 := hf.codomain_ge_2
  have h_eq : ∀ a b, a ≥ 2 → b ≥ 2 → a ≠ b → f a * f b = f (a ^ 2 * b ^ 2) := hf.functional_eq

  -- Helper lemma: f n is non-zero and positive for n ≥ 2
  have f_pos : ∀ n, n ≥ 2 → f n > 0 := by
    intro n hn
    have h : f n ≥ 2 := h_codom n hn
    linarith

  have f_ne_zero : ∀ n, n ≥ 2 → f n ≠ 0 := by
    intro n hn
    have h : f n > 0 := f_pos n hn
    linarith [h]

  -- Helper: Powers of numbers >= 2 are >= 2 (for n >= 1)
  have pow_ge_two {a : ℕ} (ha : a ≥ 2) {n : ℕ} (hn : n ≥ 1) : a ^ n ≥ 2 := by
    induction n with
    | zero => contradiction -- hn says n>=1
    | succ k ih =>
      rw [Nat.pow_succ]
      if hk : k = 0 then
        rw [hk, Nat.pow_zero]
        linarith
      else
        have hk_ge_1 : k ≥ 1 := Nat.pos_of_ne_zero hk
        have iha : a ^ k ≥ 2 := ih hk_ge_1
        calc a ^ k * a ≥ a ^ k * 2:= by rel [ha]
            _ ≥ 2 * 2     := by linarith
            _ ≥ 2         := by norm_num

  -- *** Step 1 & 2: Derive f(a^2)f(b) = f(b^2)f(a) ***
  -- The proof chooses an integer c > a and c > b and applies the functional equation.
  -- Formalizing the existence of such 'c' that also satisfies the non-equality
  -- conditions (like a^2 ≠ bc, b^2 ≠ ac, a ≠ c, b ≠ c) needed for applying h_eq
  -- is complex. We assume this part of the derivation works.
  have h_ratio_const_prop : ∀ a b : ℕ, a ≥ 2 → b ≥ 2 → f (a^2) * f b = f (b^2) * f a := by
    intro a b ha hb
    -- Proof sketch:q
    -- 1. Show exists c:ℕ such that c > a, c > b, c ≥ 2 and the needed inequalities hold
    --    (e.g., a^2 ≠ bc, b^2 ≠ ac, a ≠ c, b ≠ c, maybe others depending on exact application)
    -- 2. Apply h_eq:
    --    Let X = a^2, Y = bc. Assume X ≠ Y, X ≥ 2, Y ≥ 2. f(X)f(Y) = f(X^2 Y^2) = f(a^4 b^2 c^2)
    --    Let X = b, Y = c. Assume b ≠ c, b ≥ 2, c ≥ 2. f(b)f(c) = f(b^2 c^2)
    --    The proof text seems to imply f(a^4 b^4 c^4) = f(a^2) * f(b^2 c^2) and f(b^2 c^2) = f(b) * f(c)
    --    This requires a^2 ≠ b^2 * c^2 and b ≠ c.
    --    So f(a^4 b^4 c^4) = f(a^2) * f(b) * f(c) (under conditions on c)
    --    Similarly, f(a^4 b^4 c^4) = f(b^2) * f(a) * f(c) (under conditions on c)
    -- 3. Compare: f(a^2) * f(b) * f(c) = f(b^2) * f(a) * f(c)
    -- 4. Cancel f(c) (since f(c) ≥ 2, so f(c) ≠ 0).
    -- Handle the trivial case a = b first
    by_cases h_eq_ab : a = b
    · -- If a = b, the equation becomes f(a^2)*f(a) = f(a^2)*f(a), which is true.
      rw [h_eq_ab]
    · -- Case a ≠ b
      rename ¬a = b => hne

      have h_exists_c : ∃ c : ℕ, c ≥ 2 ∧ c ≠ a ∧ c ≠ b ∧ a^2 ≠ b^2 * c^2 ∧ b^2 ≠ a^2 * c^2 := by
        let c := max (a^2) (b^2) + 1
        use c
        refine ⟨?_, ?_, ?_, ?_, ?_⟩

        have hc_gt_2: c ≥ 2 := by
          calc
            c ≥ a^2 + 1 := Nat.add_le_add_right (Nat.le_max_left _ _) 1 -- max(x,y) ≥ x
            _ ≥ 2^2 + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left ha 2) 1 -- a ≥ 2 implies a^2 ≥ 2^2
            _ = 5 := by norm_num -- 2^2 + 1 = 4 + 1 = 5
            _ ≥ 2 := by norm_num -- 5 ≥ 2

        -- Goal 1: Prove c ≥ 2
        case h.refine_1 =>
          calc
            c ≥ a^2 + 1 := Nat.add_le_add_right (Nat.le_max_left _ _) 1 -- max(x,y) ≥ x
            _ ≥ 2^2 + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left ha 2) 1 -- a ≥ 2 implies a^2 ≥ 2^2
            _ = 5 := by norm_num -- 2^2 + 1 = 4 + 1 = 5
            _ ≥ 2 := by norm_num -- 5 ≥ 2

        -- Goal 2: Prove c ≠ a
        case h.refine_2 =>
          apply Nat.ne_of_gt -- To show c ≠ a, it suffices to show c > a
          calc
            c ≥ a^2 + 1 := Nat.add_le_add_right (Nat.le_max_left _ _) 1
            _ > a := by nlinarith

        -- Goal 3: Prove c ≠ b
        case h.refine_3 =>
          apply Nat.ne_of_gt -- To show c ≠ b, it suffices to show c > b
          calc
            c ≥ b^2 + 1 := Nat.add_le_add_right (Nat.le_max_right _ _) 1 -- max(x,y) ≥ y
            _ > b := by nlinarith

        -- Goal 4: Prove a^2 ≠ b^2 * c^2
        case h.refine_4 =>
          apply Nat.ne_of_lt
          calc
            a^2 < c := Nat.add_le_add_right (Nat.le_max_left _ _) 1
            _ <= c^2 := by nlinarith
            _ <= b ^ 2 * c ^ 2 := by
              have : b^2>=4:=by nlinarith [sq_nonneg (b - 2)]
              nlinarith

        -- Goal 5: Prove b^2 ≠ a^2 * c^2
        case h.refine_5 =>
          apply Nat.ne_of_lt
          calc
            b^2 < c := Nat.add_le_add_right (Nat.le_max_right _ _) 1
            _ <= c^2 := by nlinarith
            _ <= a ^ 2 * c ^ 2 := by
              have : a^2>=4:=by nlinarith [sq_nonneg (a - 2)]
              nlinarith

      -- Deconstruct the existential quantifier
      obtain ⟨c, hc, hca, hcb, h_neq1, h_neq2⟩ := h_exists_c

      -- Verify prerequisites for applying h_eq
      have ha2_ge_2 : a ^ 2 ≥ 2 := pow_ge_two ha (by norm_num : 1 ≤ 2)
      have hb2_ge_2 : b ^ 2 ≥ 2 := pow_ge_two hb (by norm_num : 1 ≤ 2)
      have h_b2c2_ge_2 : b ^ 2 * c ^ 2 ≥ 2 := by
        have hb2_ge_4 : b ^ 2 ≥ 4 := Nat.pow_le_pow_left hb 2
        have hc2_ge_4 : c ^ 2 ≥ 4 := Nat.pow_le_pow_left hc 2
        calc b ^ 2 * c ^ 2 ≥ 4 * 4 := Nat.mul_le_mul hb2_ge_4 hc2_ge_4
             _ = 16   := by rfl
             _ ≥ 2     := by norm_num
      have h_a2c2_ge_2 : a ^ 2 * c ^ 2 ≥ 2 := by
        have ha2_ge_4 : a ^ 2 ≥ 4 := Nat.pow_le_pow_left ha 2
        have hc2_ge_4 : c ^ 2 ≥ 4 := Nat.pow_le_pow_left hc 2
        calc a ^ 2 * c ^ 2 ≥ 4 * 4 := Nat.mul_le_mul ha2_ge_4 hc2_ge_4
             _ = 16   := by rfl
             _ ≥ 2     := by norm_num

      -- Show f(a^2) * f(b^2 * c^2) = f(b^2) * f(a^2 * c^2) by evaluating f(a^4 * b^4 * c^4)
      have h_eq_lhs : f (a ^ 2) * f (b ^ 2 * c ^ 2) = f ((a ^ 2) ^ 2 * (b ^ 2 * c ^ 2) ^ 2) := by
        apply h_eq (a ^ 2) (b ^ 2 * c ^ 2) ha2_ge_2 h_b2c2_ge_2 h_neq1
      have h_eq_rhs : f (b ^ 2) * f (a ^ 2 * c ^ 2) = f ((b ^ 2) ^ 2 * (a ^ 2 * c ^ 2) ^ 2) := by
        apply h_eq (b ^ 2) (a ^ 2 * c ^ 2) hb2_ge_2 h_a2c2_ge_2 h_neq2

      -- Simplify expressions and connect the equations
      have h_lhs_target : (a ^ 2) ^ 2 * (b ^ 2 * c ^ 2) ^ 2 = a ^ 4 * b ^ 4 * c ^ 4 := by ring
      have h_rhs_target : (b ^ 2) ^ 2 * (a ^ 2 * c ^ 2) ^ 2 = b ^ 4 * a ^ 4 * c ^ 4 := by ring
      rw [h_lhs_target] at h_eq_lhs
      rw [h_rhs_target] at h_eq_rhs
      have h_comm : a ^ 4 * b ^ 4 * c ^ 4 = b ^ 4 * a ^ 4 * c ^ 4 := by ring
      rw [h_comm] at h_eq_lhs
      have heq1 : f (a ^ 2) * f (b ^ 2 * c ^ 2) = f (b ^ 2) * f (a ^ 2 * c ^ 2) := by
        rw [h_eq_lhs, h_eq_rhs]

      -- Substitute f(b^2 * c^2) and f(a^2 * c^2) using h_eq
      have h_sub1 : f (b ^ 2 * c ^ 2) = f b * f c := by
        -- Need b ≠ c (hcb), b ≥ 2 (hb), c ≥ 2 (hc)
        have := h_eq b c hb hc (Ne.symm hcb)
        linarith
      have h_sub2 : f (a ^ 2 * c ^ 2) = f a * f c := by
        have := h_eq a c ha hc (Ne.symm hca)
        linarith

      -- Substitute into heq1 and simplify
      rw [h_sub1, h_sub2] at heq1
      have hfc_pos : f c > 0 := f_pos c hc
      nlinarith [heq1]

  -- *** Step 3: Show f(a^2) = k * f(a) relation (in Nat) ***
  -- Let b = 2 in h_ratio_const_prop
  have h2 : 2 ≥ 2 := by linarith
  let k_num := f (2^2) -- f(4)
  let k_den := f 2
  have h4_ge_2 : 2^2 ≥ 2 := pow_ge_two h2 (by norm_num) -- 4 >= 2
  have h_k_den_ge_2 : k_den ≥ 2 := h_codom 2 h2
  have h_k_num_ge_2 : k_num ≥ 2 := h_codom (2^2) (by linarith) -- 4 >= 2

  have h_k_relation : ∀ a, a ≥ 2 → f (a^2) * k_den = k_num * f a := by
    intro a ha
    specialize h_ratio_const_prop a 2 ha h2
    rw [h_ratio_const_prop] -- f(a^2)*f(2) = f(2^2)*f(a)
    -- This is f(a^2) * k_den = k_num * f a

  /- Note: The proof text introduces a rational k = f(a^2)/f(a) = k_num / k_den.
     We work in Nat: f(a^2) * k_den = k_num * f(a)
  -/

  -- *** Step 4: Derive f(ab) relation (Eq. 2 equivalent in ℕ) ***
  -- The proof text uses f(ab) = f(a)f(b)/k for a ≠ b.
  -- Let's derive the equivalent: f(ab) * k_num = f(a) * f(b) * k_den
  -- From h_eq: f a * f b = f (a^2 * b^2) = f ((a * b)^2) (requires a ≠ b)
  -- From h_k_relation: f((ab)^2) * k_den = k_num * f(ab) (requires ab ≥ 2)
  have h_prod_relation : ∀ a b, a ≥ 2 → b ≥ 2 → a ≠ b → f (a * b) * k_num = f a * f b * k_den := by
    intro a b ha hb h_ne
    have hab_ge_2 : a * b ≥ 2 := by nlinarith
    have eq1 := h_eq a b ha hb h_ne
    have eq2 := h_k_relation (a * b) hab_ge_2
    rw [Nat.mul_pow] at eq2
    rw [← eq1] at eq2 -- f a * f b * k_den = k_num * f (a * b)
    rw [Nat.mul_comm k_num (f (a * b))] at eq2
    exact eq2.symm -- f (a * b) * k_num = f a * f b * k_den

  -- *** Step 5: Show f(a) is constant ***
  -- The proof uses a chain starting f(a)f(a^2) = f(a^6) = ...
  -- We follow the alternative integer derivation outlined in the thought process.
  -- Goal: Show f(4) = f(a) * f(2) for all a ≥ 2.
  have h_fa_f2_f4 : ∀ a, a ≥ 2 → f 4 = f a * f 2 := by
    intro a ha
    -- Setup for powers of a
    have ha2 : a^2 ≥ 2 := pow_ge_two ha (by norm_num)
    have ha4 : a^4 ≥ 2 := pow_ge_two ha (by norm_num)
    have ha5 : a^5 ≥ 2 := pow_ge_two ha (by norm_num)
    have ha6 : a^6 ≥ 2 := pow_ge_two ha (by norm_num)

    -- Establish a ≠ a^n for n ≥ 2
    have h_a_ne_a_n : ∀ n : ℕ, n ≥ 2 → a ≠ a^n := by
      intro n hn
      apply ne_of_lt
      have h1: 1<a := by linarith
      have h2: 1<n := by linarith
      have h3 := Nat.pow_lt_pow_of_lt h1 h2
      simp at h3
      exact h3

    have h_a_ne_a2 : a ≠ a^2 := h_a_ne_a_n 2 (by linarith)
    have h_a_ne_a4 : a ≠ a^4 := h_a_ne_a_n 4 (by linarith)
    have h_a_ne_a5 : a ≠ a^5 := h_a_ne_a_n 5 (by linarith)

    -- 1. f a * f (a^2) = f (a^6) (using h_eq with a, a^2)
    have step1 : f a * f (a^2) = f (a^6) := by
      rw [h_eq a (a^2) ha ha2 h_a_ne_a2, ← Nat.pow_mul, ← Nat.pow_add]

    -- 2. f(a^6) * k_num = f a * f (a^5) * k_den (using h_prod_relation with a, a^5)
    have step2 := h_prod_relation a (a^5) ha ha5 h_a_ne_a5
    rw [<- pow_succ'] at step2

    -- 3. f(a^5) * k_num = f a * f (a^4) * k_den (using h_prod_relation with a, a^4)
    have step3 := h_prod_relation a (a^4) ha ha4 h_a_ne_a4
    rw [<- pow_succ'] at step3

    -- 4. f(a^4) * k_den = k_num * f (a^2) (using h_k_relation with a^2)
    have step4 := h_k_relation (a^2) ha2
    rw [<- pow_mul'] at step4

    -- Combine the equations through algebraic manipulation
    have h_combine : (f a * f (a^2)) * k_num^2 * k_den = f a * f a * k_num * f (a^2) * k_den^2:=
      calc (f a * f (a^2)) * k_num^2 * k_den
          = f (a^6) * k_num^2 * k_den := by rw [step1]
        _ = (f (a^6) * k_num) * k_num * k_den := by ring
        _ = (f a * f (a^5) * k_den) * k_num * k_den := by rw [step2]
        _ = f a * (f (a^5) * k_num) * k_den * k_den := by ring
        _ = f a * (f (a^5) * k_num) * k_den^2 := by ring
        _ = f a * (f a * f (a^4) * k_den) * k_den^2 := by rw [step3]
        _ = f a * f a * (f (a^4) * k_den) * k_den^2 := by ring
        _ = f a * f a * (k_num * f (a^2)) * k_den^2 := by rw [step4]
        _ = f a * f a * k_num * f (a^2) * k_den^2 := by ring

    -- Simplify to show k_num = f(a) * k_den
    have h_combine_simp : k_num = f a * k_den := by
      have h_f_a_pos : f a > 0 := f_pos a ha
      have h_f_a2_pos : f (a^2) > 0 := f_pos (a^2) ha2
      have h_X_pos : f a * f (a^2) > 0 := Nat.mul_pos h_f_a_pos h_f_a2_pos
      have h_k_den_pos : k_den > 0 := f_pos 2 h2

      apply Nat.eq_of_mul_eq_mul_right h_X_pos
      apply Nat.eq_of_mul_eq_mul_right h_k_den_pos
      apply Nat.eq_of_mul_eq_mul_right h_f_a_pos
      -- Rearrange factors on both sides of the equation to match the target form
      rw [mul_comm] at h_combine
      rw [mul_comm]
      -- Apply linear arithmetic to complete the proof
      nlinarith [h_combine]

    -- Substitute back definitions
    simp only [show k_num = f 4 by rfl, show k_den = f 2 by rfl] at h_combine_simp
    exact h_combine_simp -- f 4 = f a * f 2

  -- *** Step 6: Use f(4) = f(a) * f(2) to show f is constant ***
  have h_f4_f2_f2 : f 4 = f 2 * f 2 := by
    specialize h_fa_f2_f4 2 h2
    exact h_fa_f2_f4

  have h_f_is_const : ∀ a, a ≥ 2 → f a = f 2 := by
    intro a ha
    specialize h_fa_f2_f4 a ha -- f(4) = f a * f 2
    rw [h_f4_f2_f2] at h_fa_f2_f4 -- f 2 * f 2 = f a * f 2
    have h_f2_pos : 0 < f 2 := f_pos 2 h2
    -- Cancel f 2 using Nat.eq_of_mul_eq_mul_right
    symm at h_fa_f2_f4 -- f a * f 2 = f 2 * f 2
    rw [Nat.mul_comm (f 2) (f 2)] at h_fa_f2_f4 -- f a * f 2 = f 2 * f 2 (no change needed)
    exact Nat.eq_of_mul_eq_mul_right h_f2_pos h_fa_f2_f4

  -- *** Step 7: Final Contradiction ***
  -- We have shown f(a) = f(2) for all a ≥ 2. Let c = f(2).
  let c := f 2
  have hc_ge_2 : c ≥ 2 := h_codom 2 h2
  have hf_const : ∀ a, a ≥ 2 → f a = c := h_f_is_const

  -- Take a=2, b=3. They are ≥ 2 and 2 ≠ 3.
  have h3 : 3 ≥ 2 := by linarith
  have h2_ne_3 : 2 ≠ 3 := by decide
  have eq_23 := h_eq 2 3 h2 h3 h2_ne_3
  simp at eq_23

  -- Substitute using f(a) = c
  have hf2 : f 2 = c := hf_const 2 h2
  have hf3 : f 3 = c := hf_const 3 h3
  have h36_ge_2 : 36 ≥ 2 := by linarith
  have hf36 : f 36 = c := hf_const 36 h36_ge_2

  -- Equation becomes c * c = c
  rw [hf2, hf3, hf36] at eq_23
  have h_c_sq_eq_c : c * c = c := eq_23
  have hc_pos : 0 < c := f_pos 2 h2

  -- From c * c = c and c > 0, deduce c = 1
  have hc_eq_1 : c = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hc_pos     -- Apply left multiplication cancellation law (requires c ≠ 0)
                                              -- The goal becomes c * c = c * 1
    rw [mul_one c]                             -- Rewrite the goal as c * c = c
    exact h_c_sq_eq_c

  -- We have c = 1 and c ≥ 2. This is a contradiction.
  have h_contra : c ≥ 2 ∧ c = 1 := And.intro hc_ge_2 hc_eq_1
  linarith -- Contradiction found by linarith (1 >= 2 is false)
