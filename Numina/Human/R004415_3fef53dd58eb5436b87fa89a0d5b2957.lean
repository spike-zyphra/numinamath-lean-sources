import Mathlib

/- $\begin{array}{l}\text { 9. (16 points) Given } a, b, c \in \mathbf{R}, \\ \{a, b, c\}=\left\{-a^{3}, a b c-b^{3}, 2 a b c-c^{3}\right\}. \\ \text { Find }\{a, b, c\}.\end{array}$ -/
theorem algebra_263261 {a b c : ℝ} (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c)
  (h : ({a, b, c} : Finset ℝ) = {- a ^ 3, a * b * c - b ^ 3, 2 * a * b * c - c ^ 3}) :
  ({a, b, c} : Finset ℝ) = {-1, 0, 1} := by
  -- Decompose the set for use with Finset.sum_insert.
  have h0 : {- a ^ 3, a * b * c - b ^ 3, 2 * a * b * c - c ^ 3} =
    ({- a ^ 3} : Finset ℝ) ∪ {a * b * c - b ^ 3, 2 * a * b * c - c ^ 3} := by
    ext x; tauto
  -- Establish that the cardinality of the set {a, b, c} is 3.
  have h_card : ({a, b, c} : Finset ℝ).card = 3 := by
    refine Finset.card_eq_three.mpr ?_
    use a, b, c
    -- This follows from the hypothesis that a, b, and c are distinct.
    simp [habc]
  -- Show that the elements of the second set are distinct for `Finset.prod_insert` and `Finset.sum_insert`.
  have h_notin : a * b * c - b ^ 3 ∉ ({-a ^ 3} : Finset ℝ) ∪ {2 * a * b * c - c ^ 3} := by
    simp [Finset.not_mem_union]
    constructor <;>
    { by_contra! h1
      -- Assume for contradiction they are not distinct.
      simp [h1] at h
      -- This would imply the cardinality is at most 2.
      have : ({a, b, c} : Finset ℝ).card ≤ 2 := by
        rw [h]
        exact Finset.card_le_two
      -- This contradicts `h_card`.
      linarith}
  -- Decompose the set {a, b, c} for sum and product calculations.
  have h_union : {a, b, c} = ({a, b} : Finset ℝ) ∪ {c} := by
      ext x; simp
  -- Show that `a` is not in `{b, c}`.
  have h₀ : a ∉ ({b} : Finset ℝ) ∪ {c} := by
    simp [Finset.not_mem_union]
    exact ⟨habc.1, habc.2.2⟩
  -- The sum of elements is invariant under the equality of the sets.
  have h1 : a + b + c = -a^3 - b^3 - c^3 + 3 * a * b * c := by
    suffices a + b + c = ∑ x in {a, b, c}, x by
      -- Substitute the given equality of sets `h`.
      simp [this, h, h0]
      -- Expand the sum over the union of sets.
      rw [Finset.sum_insert h_notin, Finset.sum_union]
      simp [add_assoc]
      -- The result follows from algebraic manipulation.
      ring
      -- This part handles a side goal for disjointness.
      simp
      by_contra! h1
      -- Assume for contradiction the sets are not disjoint.
      simp [h1] at h
      -- This leads to a contradiction on cardinality.
      have : ({a, b, c} : Finset ℝ).card ≤ 2 := by
        rw [h]
        exact Finset.card_le_two
      linarith
    simp [h_union]
    -- Expand the sum over the decomposed set.
    rw [Finset.sum_insert h₀, Finset.sum_union]
    simp [add_assoc]
    -- Prove disjointness needed for `sum_union`.
    refine Finset.disjoint_singleton.mpr habc.2.1
  -- The product of elements is also invariant under the equality of the sets.
  have h2 : a * b * c = (-a^3) * (a * b * c - b ^ 3) * (2 * a * b * c - c ^ 3) := by
    suffices a * b * c = ∏ x in {a, b, c}, x by
      -- Substitute the set equality `h`.
      nth_rw 1 [this, h, h0]
      simp
      -- Expand the product over the union.
      rw [Finset.prod_insert h_notin, Finset.prod_union]
      simp [add_assoc]
      -- Algebraic simplification.
      ring
      -- Side goal for disjointness.
      simp
      by_contra! h1
      -- Assume for contradiction.
      simp [h1] at h
      -- Contradiction on cardinality again.
      have : ({a, b, c} : Finset ℝ).card ≤ 2 := by
        rw [h]
        exact Finset.card_le_two
      linarith
    simp [h_union]
    -- Expand the product over the decomposed set.
    rw [Finset.prod_insert h₀, Finset.prod_union]
    simp [mul_assoc]
    -- Prove disjointness needed for `prod_union`.
    refine Finset.disjoint_singleton.mpr habc.2.1
  -- This identity follows from the sum of cubes factorization.
  have h3 : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 + 2) / 2 = 0 := by
    -- Rearrange the sum identity `h1`.
    rw [← neg_add', ← neg_add', add_comm _ (3 * a * b * c)] at h1
    simp [← sub_eq_zero] at h1
    -- Substitute `h1` into the identity.
    rw [← h1]
    ring
  -- A product is zero iff one of its factors is zero.
  rw [mul_div_assoc, mul_eq_zero] at h3
  -- Case split on which factor is zero.
  rcases h3 with h3 | h3
  -- Case 1: a + b + c = 0.
  · by_cases habc' : a * b * c = 0
    -- Subcase 1.1: The product a * b * c is zero.
    · rw [mul_assoc 2 _ _, mul_assoc 2 _ _, habc', mul_zero, zero_sub, zero_sub] at h
      -- Clean up unused hypotheses.
      clear h0 h_card h_notin h_union h₀ h1 h2
      -- Assume without loss of generality that a = 0.
      wlog h_a_is_zero : a = 0
      -- The `wlog` tactic requires proving the other cases follow.
      · have : b = 0 ∨ c = 0 := by
          by_contra! h1
          suffices a * b * c ≠ 0 by exact this habc'
          apply mul_ne_zero _ h1.2
          apply mul_ne_zero h_a_is_zero h1.1
        rcases this with hb_zero | hc_zero
        -- Case b = 0.
        · have h1 : ({b, a, c} : Finset ℝ) = {a, b, c} := by
            ext _; simp; tauto
          have h2 : ({b, a, c} : Finset ℝ) = {-b ^ 3, -a ^ 3, -c ^ 3} := by
            simp [h1, h]
            ext x; simp; tauto
          -- Recurse on the theorem with b = 0.
          specialize this ⟨Ne.symm habc.1, habc.2.2, habc.2.1⟩ h2 (by linarith) (by linarith) hb_zero
          simp [← h1, this]
        -- Case c = 0.
        · have h1 : ({c, a, b} : Finset ℝ) = {a, b, c} := by
            ext _; simp; tauto
          have h2 : ({c, a, b} : Finset ℝ) = {-c ^ 3, -a ^ 3, -b ^ 3} := by
            simp [h1, h]
            ext x; simp; tauto
          -- Recurse on the theorem with c = 0.
          specialize this ⟨Ne.symm habc.2.2, habc.1, Ne.symm habc.2.1⟩ h2 (by linarith) (by linarith) hc_zero
          simp [← h1, this]
      -- Now we work with the assumption a = 0.
      · subst h_a_is_zero
        -- From a + b + c = 0 and a = 0, we get c = -b.
        have h_c_eq_neg_b : c = -b := by linarith [h3]
        subst h_c_eq_neg_b
        -- Substitute these equalities into our hypotheses.
        simp at h habc
        -- b cannot be 0 because a=0 and a≠b.
        have h_b_ne_zero : b ≠ 0 := by tauto
        -- b must be an element of the resulting set.
        have h_b_mem : b ∈ ({0, -b ^ 3, -(-b) ^ 3} : Finset ℝ) := by simp [← h]
        simp at h_b_mem
        -- Case split on which element b equals.
        rcases h_b_mem with h_b_case | h_b_case | h_b_case
        -- Case b = 0, a contradiction.
        · tauto
        -- Case b = -b^3.
        · have : b * (b^2 + 1) = 0 := by
            rw [← sub_eq_zero] at h_b_case
            rw [← h_b_case]
            ring
          -- Since b≠0, b^2+1=0.
          have h_impossible : b^2 + 1 = 0 := (mul_eq_zero.mp this).resolve_left h_b_ne_zero
          -- This is impossible for a real number b.
          exfalso; nlinarith
        -- Case b = b^3.
        · have : b * (b^2 - 1) = 0 := by
            rw [← sub_eq_zero] at h_b_case
            simp at h_b_case
            rw [show (0 : ℝ) = -0 by simp, ← h_b_case]
            ring
          -- Since b≠0, b^2=1.
          have h_b_sq_eq_one : b^2 = 1 := by linarith [(mul_eq_zero.mp this).resolve_left h_b_ne_zero]
          -- This means b is 1 or -1.
          rcases sq_eq_one_iff.mp h_b_sq_eq_one with hb1 | hbn1
          -- If b = 1, then {a,b,c} = {0, 1, -1}.
          · simp [hb1]
            ext x; simp; tauto
          -- If b = -1, then {a,b,c} = {0, -1, 1}.
          · simp [hbn1]
            ext x; simp; tauto
    -- Subcase 1.2: The product a * b * c is not zero.
    · have h2 := Eq.symm h2
      rw [← div_eq_one_iff_eq (by simp [habc']), mul_div_mul_comm, mul_div_mul_comm] at h2
      -- Field simplifications, valid since a,b,c are non-zero.
      have h4 : -a ^ 3 / a = -a^2 := by
        by_cases ha : a = 0
        · simp [ha]
        · field_simp [ha]
          ring_nf
      have h5 : (a * b * c - b ^ 3) / b = (a * c - b ^ 2) := by
        by_cases hb : b = 0
        · simp [hb] at habc'
        · field_simp [hb]
          ring_nf
      have h6 : (2 * a * b * c - c ^ 3) / c = (2 * a * b - c ^ 2) := by
        by_cases hc : c = 0
        · simp [hc] at habc'
        · field_simp [hc]
          ring_nf
      -- Use a+b+c=0 to substitute for b and c.
      have h7 : b ^ 2 = (a + c) ^ 2 := by
        suffices b = -(a + c) by rw [this]; exact neg_pow_two (a + c)
        linarith
      have h8 : c ^ 2 = (a + b) ^ 2 := by
        suffices c = -(a + b) by rw [this]; exact neg_pow_two (a + b)
        linarith
      simp [h4, h5, h6, h7, h8] at h2
      -- A complex algebraic identity.
      have h9 : -(a ^ 2 * (a * c - (a + c) ^ 2) * (2 * a * b - (a + b) ^ 2)) =
        -a ^ 2 * ((a + c / 2) ^ 2 + 3 * c ^ 2 / 4) * (a ^ 2 + b ^ 2) := by ring
      rw [h9] at h2
      -- This branch leads to a contradiction as it tries to prove 1 <= 0.
      suffices -a ^ 2 * ((a + c / 2) ^ 2 + 3 * c ^ 2 / 4) * (a ^ 2 + b ^ 2) ≤ 0 by linarith
      apply mul_nonpos_of_nonpos_of_nonneg _ (by positivity)
      apply mul_nonpos_of_nonpos_of_nonneg _ (by positivity)
      simp
      positivity
  -- Case 2: The other factor is zero.
  · -- This is impossible as it is a sum of squares plus 2.
    nlinarith