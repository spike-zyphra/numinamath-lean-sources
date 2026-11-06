import Mathlib

/- Let $u_{1}, u_{2}, \ldots, u_{2019}$ be real numbers satisfying $$ u_{1}+u_{2}+\cdots+u_{2019}=0 \quad \text { and } \quad u_{1}^{2}+u_{2}^{2}+\cdots+u_{2019}^{2}=1 $$ Let $a=\min \left(u_{1}, u_{2}, \ldots, u_{2019}\right)$ and $b=\max \left(u_{1}, u_{2}, \ldots, u_{2019}\right)$. Prove that $$ a b \leqslant-\frac{1}{2019} $$  -/

theorem inequalities_23824 (ia: Fin 2019) (ib: Fin 2019) (u : Fin 2019 → ℝ) (hsum : ∑ i, u i = 0) (hsq : ∑ i, (u i)^2 = 1) (ha: ∀ i : Fin 2019, u ia ≤ u i) (hb: ∀ i : Fin 2019, u i ≤ u ib): (u ia) * (u ib) ≤ -1 / 2019 := by

  -- Define a and b as the minimum and maximum values in u
  set a := u ia
  set b := u ib

  -- Define the sets of positive and non-positive indices
  let P := Finset.filter (fun i => u i > 0) Finset.univ
  let N := Finset.filter (fun i => u i ≤ 0) Finset.univ

  have u_exist_pos: ∃ i, u i > 0 := by
    -- Start proof by contradiction
    by_contra u_not_exist_pos
    -- Simplify the negation: ¬(∃ i, u i > 0) becomes ∀ i, ¬(u i > 0), which is ∀ i, u i ≤ 0
    push_neg at u_not_exist_pos
    -- Apply the theorem: If a sum of non-positive terms is zero, all terms must be zero.
    -- The theorem is Finset.sum_eq_zero_iff_of_nonpos
    -- We need to provide the proof that each term u i is non-positive, which is exactly u_not_exist_pos i
    rw [Finset.sum_eq_zero_iff_of_nonpos (fun i hi => u_not_exist_pos i)] at hsum
    -- Now hsum is equivalent to ∀ i ∈ s, u i = 0
    -- Use this fact (that all u i in s are 0) to simplify hsq
    -- If all u i = 0, then (u i)^2 = 0, and the sum of squares should be 0.
    -- simp will substitute u i = 0 into the sum in hsq
    simp [hsum] at hsq
    -- hsq becomes Finset.sum s (fun i => (0 : β)^2) > 0
    -- which simplifies to Finset.sum s (fun i => 0) > 0
    -- which simplifies to 0 > 0, which is a contradiction (False).
    -- The contradiction proves the original statement.



  have u_exist_neg : ∃ i, u i < 0 := by
    by_contra u_not_exist_neg
    push_neg at u_not_exist_neg
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => u_not_exist_neg i)] at hsum
    simp [hsum] at hsq

  have a_neg : a < 0 := by
    -- Since we know ∑i, u i = 0 and ∑i, (u i)^2 = 1, u cannot be constantly 0
    -- We already have u_not_all_zero : ¬ (∀ i, u i = 0)
    -- And we already have u_exist_neg : ∃ i, u i < 0
    obtain ⟨i, hi⟩ := u_exist_neg
    -- By definition, a is the infimum of the range of u
    -- have ha : a ≤ u i := a_le_u_i i
    -- Since u i < 0, we have a ≤ u i < 0
    exact lt_of_le_of_lt (ha i) hi

  have b_pos : 0 < b := by
    -- Since we know ∑i, u i = 0 and ∑i, (u i)^2 = 1, u cannot be constantly 0
    -- We already have u_not_all_zero : ¬ (∀ i, u i = 0)
    -- And we already have u_exist_pos : ∃ i, u i > 0
    obtain ⟨i, hi⟩ := u_exist_pos
    -- By definition, b is the supremum of the range of u
    -- have hb0 : u i ≤ b := hb i
    -- Since u i > 0, we have b ≥ u i > 0
    exact lt_of_lt_of_le hi (hb i)

  have P_union_N: P ∪ N = Finset.univ := by
    ext i
    simp [P, N]
    exact lt_or_ge 0 (u i)

  have P_inter_N: P ∩ N = ∅ := by
    ext i
    simp [P, N]

  -- Define sizes p and n
  let p := P.card
  let n := N.card

  -- Then we have p + n = 2019
  have h_card : p + n = 2019 := by
    rw [← Finset.card_union_add_card_inter P N]
    rw [P_union_N, Finset.card_univ]
    rw [P_inter_N, Finset.card_empty, add_zero, Fintype.card_fin (n := 2019)]

  -- Sum of positive elements equals sum of absolute values of non-positive elements
  have sum_eq : ∑ i ∈ P, u i = ∑ i ∈ N, |u i| := by
    have h₁ : ∑ i ∈ P, u i + ∑ i ∈ N, u i = 0 := by
      -- Decomposing by universal set, proving that the sum over P and N equals the sum over the universal set
      -- The sum of all elements equals 0 (condition hsum)

      -- Proving that the universal sum equals the sum over P and N
      have sum_decomp : ∑ i, u i = ∑ i ∈ P, u i + ∑ i ∈ N, u i := by
        have : ∑ i, u i = ∑ i ∈ Finset.univ, u i := by rfl
        rw [this]
        rw [← P_union_N]
        rw [Finset.sum_union]
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact P_inter_N

      -- Using the original condition hsum : ∑ i, u i = 0
      rw [sum_decomp] at hsum
      exact hsum

    -- Converting the sum of non-positive numbers to the sum of absolute values
    have h₂ : ∑ i ∈ N, u i = -∑ i ∈ N, |u i| := by
      rw [← Finset.sum_neg_distrib]
      apply Eq.symm
      apply Finset.sum_congr rfl
      intro i hi_nonpos
      rw [abs_of_nonpos]
      rw [neg_neg]
      -- From the definition of N, if i ∈ N, then u i ≤ 0
      exact (Finset.mem_filter.mp hi_nonpos).2

    -- Combining the above steps, we get that the sum of positive numbers equals the sum of absolute values of non-positive numbers
    linarith [h₁, h₂]


  -- Estimate the sum of squares for positive elements
  -- \sum_{i \in P} u_{i}^{2} \leqslant \sum_{i \in P} b u_{i}=b \sum_{i \in P} u_{i}=b \sum_{i \in N}\left|u_{i}\right| \leqslant b \sum_{i \in N}|a|=-n a b
  have pos_sq_est : ∑ i ∈ P, (u i)^2 ≤ -n*a*b:= by
    -- Step 1: For all i ∈ P, u i > 0 and u i ≤ b, so (u i)^2 ≤ b * u i
    have h1 : ∀ (i : Fin 2019), i ∈ P → (u i)^2 ≤ b * u i := by
      intros i hi
      have u_i_pos : 0 < u i := (Finset.mem_filter.mp hi).2
      -- u i ≤ b since b is the maximum value
      -- have ub : u i ≤ b := u_i_le_b i
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hb i) (le_of_lt u_i_pos)

    -- Apply over the sum
    have sum_ineq : ∑ i ∈ P, (u i)^2 ≤ ∑ i ∈ P, b * u i := by
      apply Finset.sum_le_sum
      exact h1

    -- Factor out b
    -- have factor2 : ∑ i ∈ P, u i * b = (∑ i ∈ P, u i) * b := by
    --   rw [<- Finset.sum_mul]

    have factor : ∑ i ∈ P, b * u i = b * ∑ i ∈ P, u i := by
      rw [← Finset.mul_sum]

    -- Use the equality ∑ i ∈ P, u i = ∑ i ∈ N, |u i|
    have sum_eq_abs : b * ∑ i ∈ P, u i = b * ∑ i ∈ N, |u i| := by
      rw [sum_eq]

    -- For all i ∈ N, u i ≤ 0 and a ≤ u i, so |u i| = -u i ≤ -a
    have h2 : ∀ (i : Fin 2019), i ∈ N → |u i| ≤ -a := by
      intros i hi
      have u_i_nonpos : u i ≤ 0 := (Finset.mem_filter.mp hi).2
      -- a ≤ u i since a is the minimum value
      have : a ≤ u i := ha i
      rw [abs_of_nonpos u_i_nonpos]
      linarith [a_neg]

    -- Apply over the sum
    have abs_sum_ineq : ∑ i ∈ N, |u i| ≤ ∑ i ∈ N, -a := by
      apply Finset.sum_le_sum
      exact h2

    -- Multiply by b (which is positive)
    have mul_ineq : b * ∑ i ∈ N, |u i| ≤ b * ∑ i ∈ N, -a := by
      apply mul_le_mul_of_nonneg_left
      · exact abs_sum_ineq
      · exact le_of_lt b_pos

    -- Simplify the final term
    have simplify : b * ∑ i ∈ N, -a = -n * a * b := by
      rw [Finset.sum_const]
      ring

    -- Combine everything
    calc
      ∑ i ∈ P, (u i)^2 ≤ ∑ i ∈ P, b * u i := sum_ineq
      _ = b * ∑ i ∈ P, u i := factor
      _ = b * ∑ i ∈ N, |u i| := sum_eq_abs
      _ ≤ b * ∑ i ∈ N, -a := mul_ineq
      _ = -n * a * b := simplify


  -- Estimate the sum of squares for non-positive elements
  -- \sum_{i \in N} u_{i}^{2} \leqslant \sum_{i \in N}|a| \cdot\left|u_{i}\right|=|a| \sum_{i \in N}\left|u_{i}\right|=|a| \sum_{i \in P} u_{i} \leqslant|a| \sum_{i \in P} b=-p a b
  have neg_sq_est : ∑ i ∈ N, (u i)^2 ≤ -p*a*b:= by
    -- Step 1: For all i ∈ N, u i ≤ 0 and a ≤ u i. Then (u i)^2 = |u i|^2 and |u i| = -u i ≤ -a.
    -- So (u i)^2 = |u i| * |u i| ≤ (-a) * |u i| because |u i| ≥ 0 and -a > 0.
    have h1 : ∀ (i : Fin 2019), i ∈ N → (u i)^2 ≤ (-a) * |u i| := by
      intros i hi
      have u_i_nonpos : u i ≤ 0 := (Finset.mem_filter.mp hi).2
      have h_a_le_ui : a ≤ u i := ha i
      -- We know a ≤ u i ≤ 0 => 0 ≤ -u i ≤ -a
      have abs_le : |u i| ≤ -a := by
        rw [abs_of_nonpos u_i_nonpos]
        linarith -- uses h_a_le_ui implicitly
      -- Now show (u i)^2 ≤ (-a) * |u i|
      calc
        (u i)^2 = |u i|^2             := by rw [sq_abs] -- (u i)^2 = |u i|^2
        _       = |u i| * |u i|       := by rw [pow_two]
        _       ≤ |u i| * (-a)       := by
                    apply mul_le_mul_of_nonneg_left -- Need |u i| ≥ 0
                    · exact abs_le -- |u i| ≤ -a
                    · exact abs_nonneg (u i) -- |u i| ≥ 0
        _       = (-a) * |u i|       := by rw [mul_comm]

    -- Apply over the sum
    have sum_ineq : ∑ i ∈ N, (u i)^2 ≤ ∑ i ∈ N, (-a) * |u i| := by
      apply Finset.sum_le_sum
      exact h1

    -- Factor out (-a)
    have factor : ∑ i ∈ N, (-a) * |u i| = (-a) * ∑ i ∈ N, |u i| := by
      rw [Finset.mul_sum] -- Use Finset.mul_sum

    -- Use the equality ∑ i ∈ N, |u i| = ∑ i ∈ P, u i
    have sum_eq_abs : (-a) * ∑ i ∈ N, |u i| = (-a) * ∑ i ∈ P, u i := by
      rw [sum_eq] -- Apply the assumption in reverse

    -- For all i ∈ P, u i > 0 and u i ≤ b
    have h2 : ∀ (i : Fin 2019), i ∈ P → u i ≤ b := by
      intros i hi
      -- u i ≤ b since b is the maximum value
      exact hb i

    -- Apply over the sum: ∑ i ∈ P, u i ≤ ∑ i ∈ P, b
    have sum_le_b_sum : ∑ i ∈ P, u i ≤ ∑ i ∈ P, b := by
      apply Finset.sum_le_sum
      exact h2

    -- Multiply by (-a) (which is positive since a < 0)
    have mul_ineq : (-a) * ∑ i ∈ P, u i ≤ (-a) * ∑ i ∈ P, b := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_le_b_sum
      · linarith [a_neg] -- -a > 0

    -- Simplify the final term
    have simplify : (-a) * ∑ i ∈ P, b = -p * a * b := by
      rw [Finset.sum_const] -- Use card_P
      ring -- Rearrange terms: (-a) * (p * b) = -(p * a * b)

    -- Combine everything
    calc
      ∑ i ∈ N, (u i)^2 ≤ ∑ i ∈ N, (-a) * |u i| := sum_ineq
      _ = (-a) * ∑ i ∈ N, |u i|       := factor
      _ = (-a) * ∑ i ∈ P, u i         := sum_eq_abs
      _ ≤ (-a) * ∑ i ∈ P, b           := mul_ineq
      _ = -p * a * b                   := simplify

  -- Combine the estimates
  --  1=\sum_{i=1}^{2019} u_{i}^{2}=\sum_{i \in P} u_{i}^{2}+\sum_{i \in N} u_{i}^{2} \leqslant-(p+n) a b=-2019 a b ;
  have total_sq_est : 1 ≤ -2019*a*b := by
    -- Conversion theorem: According to hsq, 1 = ∑ i, (u i)^2
    have sum_eq_one : 1 = ∑ i, (u i)^2 := by
      rw [hsq]

    -- Decompose the sum over P and N
    have sum_split : ∑ i, (u i)^2 = ∑ i ∈ P, (u i)^2 + ∑ i ∈ N, (u i)^2 := by
      -- Convert the total sum to a sum over Finset.univ
      have univ_sum : ∑ i, (u i)^2 = ∑ i ∈ Finset.univ, (u i)^2 := rfl
      -- Use P ∪ N = Finset.univ
      rw [univ_sum, ← P_union_N]
      -- Use P ∩ N = ∅ to prove P and N are disjoint
      apply Finset.sum_union
      apply Finset.disjoint_iff_inter_eq_empty.mpr
      exact P_inter_N

    -- Using the previous estimates: ∑ i ∈ P, (u i)^2 ≤ -n*a*b, ∑ i ∈ N, (u i)^2 ≤ -p*a*b
    have sum_le : ∑ i ∈ P, (u i)^2 + ∑ i ∈ N, (u i)^2 ≤ -n*a*b + (-p*a*b) := by
      apply add_le_add
      · exact pos_sq_est
      · exact neg_sq_est

    -- Combining all the above results
    calc
      1 = ∑ i, (u i)^2 := sum_eq_one
      _ = ∑ i ∈ P, (u i)^2 + ∑ i ∈ N, (u i)^2 := sum_split
      _ ≤ -n*a*b + (-p*a*b) := sum_le
      _ = -(n+p)*a*b := by ring
      _ = -2019*a*b := by
        rw [<- Nat.cast_add]
        rw [add_comm]
        rw [h_card]
        field_simp


  -- Final inequality derivation
  have final_ineq : a * b ≤ -1 / 2019 := by
    linarith

  exact final_ineq
