import Mathlib

open Finset Filter

/-Find all positive real numbers $\lambda$ such that every sequence $a_{1}, a_{2}, \ldots$ of positive real numbers satisfying

$$
a_{n+1}=\lambda \cdot \frac{a_{1}+a_{2}+\ldots+a_{n}}{n}
$$

for all $n \geq 2024^{2024}$ is bounded.
Remark: A sequence $a_{1}, a_{2}, \ldots$ of positive real numbers is bounded if there exists a real number $M$ such that $a_{i}< M$ for all $i=1,2, \ldots$
Answer: All positive real numbers $\lambda \leq 1$.-/
theorem algebra_605102 (l : ℝ) (lpos : 0 < l) (m : ℕ) (meq : m = 2024 ^ 2024) :
  (∀ a : ℕ → ℝ, (∀ i, 0 < a i) → (∀ n ≥ m, a n =
  l * (∑ i ∈ range n, a i) / n) → BddAbove (a '' Set.univ)) ↔ l ≤ 1 := by
-- Generalize $2024 ^ 2024$ to any natural number greater than $1$
  have mgt : 1 < m := by
    rw [meq]; apply Nat.one_lt_pow; all_goals norm_num
  clear meq; constructor
  -- Contrapose the goal, we show that if $l>1$, there exists an unbounded sequence $a_n$ satisfying the conditions in question
  · contrapose!; intro lgt
  -- The auxillary sequence $b_i$ corresponding to the terms of $a_i$ starting from $m$
    let b : ℕ → ℝ := fun i => by induction i with
    | zero => exact l
    | succ i bi => exact bi * (1 + (l - 1) / (i + m + 1))
    have bsucc : ∀ i, b (i + 1) = b i * (1 + (l - 1) / (i + m + 1)) := by simp [b]
  -- Use induction to show that the sequence $b_i$ has a summation property
    have bsum : ∀ t, b t = (l * ∑ x ∈ range (t + m), if x < m then 1 else b (x - m)) / ↑(t + m) := by
      intro t; induction t with
      | zero =>
        rw [sum_ite_of_true]; simp [b]
        rw [mul_div_cancel_right₀]
        positivity; simp
      | succ t iht =>
        by_cases ht: t = 0
        · simp [ht]; rw [add_comm, sum_range_succ]
          simp [b, sum_ite_of_true]; field_simp; ring
        rw [bsucc, show t+1+m = t+m+1 by omega]
        rw [sum_range_succ]; split; omega
        rw [eq_div_iff] at iht; nth_rw 2 [mul_comm] at iht
        rw [← div_eq_iff] at iht; rw [← iht]; push_cast
        rw [Nat.add_sub_cancel]; field_simp; ring
        all_goals positivity
  -- Define $a$ to be the sequence with first $m$ terms $1$, and the rest terms given by $b_(i-m)$
    let a : ℕ → ℝ := fun i => if i < m then 1 else b (i - m)
    use a; split_ands
    -- Prove that $a$ is positive by induction
    · intro i; simp [a]; split_ifs
      norm_num; induction i with
      | zero => omega
      | succ i ih =>
        by_cases hi : i < m
        · replace hi : i = m - 1 := by omega
          rw [hi, Nat.sub_add_cancel, Nat.sub_self]
          simp [b]; exact lpos; omega
        specialize ih hi; simp [b] at ih
        rw [Nat.sub_add_comm]; simp [b]
        rw [Nat.recAux_succ]; apply mul_pos
        · exact ih
        apply add_pos_of_pos_of_nonneg; norm_num
        apply div_nonneg; linarith only [lgt]
        norm_cast; all_goals omega
    -- Prove that $a_n$ has a summation formula
    · intro n hn; simp [a]; split_ifs; omega
      nth_rw 2 [show n = n-m+m by omega]
      nth_rw 3 [show n = n-m+m by omega]
      apply bsum
  -- Prove that $a_n$ is not bounded above, we first show that for terms with index greater than $m$, $a_(m+k)$ has a product formula
  -- We will proceed by induction
    have aux : ∀ k, a (m + k) = l * ∏ i ∈ range k, (1 + (l - 1) / (i + m + 1)) := by
      intro k; induction k with
      | zero => simp [a, b]
      | succ k ihk =>
        dsimp [a]; split_ifs with h'; linarith only [h']
        dsimp [a] at ihk; split_ifs at ihk with h'
        linarith only [h']; rw [prod_range_succ]
        rw [show m+k-m = k by omega] at ihk
        rw [show m+(k+1)-m = k+1 by omega, bsucc]
        rw [mul_one_add, ← mul_assoc, mul_add, ← ihk]
        field_simp
  -- Use the product formula to show that $a_(m+k)$ is greater than a real multiple of a harmonic summation
    replace aux : ∀ k > 0, l * (l - 1) * (∑ i ∈ range k, ((i : ℝ) + m + 1)⁻¹) < a (m + k) := by
      intro k kpos; by_cases hk : k ≤ 1
      · replace hk : k = 1 := by omega
        simp [hk, a, b]; field_simp
        gcongr; linarith only [mgt]
      rw [aux, prod_one_add]
      let s : ℕ → Finset ℕ := fun i => {i}
      have simg : image s (range k) ⊆ (range k).powerset := by simp [subset_iff, s]
      have : l * ∑ t ∈ image s (range k), ∏ i ∈ t, (l - 1) / (i + m + 1) <
      l * ∑ t ∈ (range k).powerset, ∏ i ∈ t, (l - 1) / (i + m + 1) := by
        rw [mul_lt_mul_left lpos]
        apply sum_lt_sum_of_subset simg
        · have : {0, 1} ∈ (range k).powerset := by
            simp [subset_iff]; constructor; all_goals omega
          exact this
        · simp [s]; intros; intro h
          apply_fun fun t => t.card at h; simp at h
        · simp; replace lgt : 0 < l - 1 := by linarith only [lgt]
          positivity
        · intros; replace lgt : 0 < l - 1 := by linarith only [lgt]
          positivity
      apply lt_of_le_of_lt _ this
      rw [mul_assoc, mul_le_mul_left, mul_sum]
      simp [s, ← div_eq_mul_inv]; exact lpos
  -- Rewrite the goal by unfolding the definition of `BddAbove`
    simp [bddAbove_def]; intro B
    suffices : ∃ u > 0, B < l * (l - 1) * ∑ i ∈ range u, ((i : ℝ) + m + 1)⁻¹
    · rcases this with ⟨u, ⟨upos, hu⟩⟩
      use m+u; specialize aux u upos
      linarith only [aux, hu]
  -- Apply the divergence of the harmonic sum, the goal follows
    let g : ℕ → ℝ := fun n => (n : ℝ) ⁻¹
    have harm : ¬Summable g := by dsimp [g]; exact Real.not_summable_natCast_inv
    replace harm : ¬Summable (fun n => g (n + (m + 1))) := by
      intro h; apply Summable.comp_nat_add at h; contradiction
    rw [not_summable_iff_tendsto_nat_atTop_of_nonneg] at harm
    rw [tendsto_atTop_atTop] at harm; simp [g, ← add_assoc] at harm
    specialize harm (B / (l * (l - 1)) + 1); rcases harm with ⟨u', hu'⟩
    specialize hu' u' (by rfl); let u := u' ⊔ 1; use u
    constructor
    · have : 1 ≤ u := by exact Nat.le_max_right u' 1
      linarith only [this]
    replace hu' : B < l * (l - 1) * ∑ x ∈ range u', ((x : ℝ) + m + 1)⁻¹ := by
      rw [← div_lt_iff₀']; linarith only [hu']
      replace lgt : 0 < l - 1 := by linarith only [lgt]
      positivity
    apply lt_of_lt_of_le hu'; rw [mul_le_mul_left]
    apply sum_le_sum_of_subset_of_nonneg
    · simp; exact Nat.le_max_left u' 1
    · intros; positivity
    · replace lgt : 0 < l - 1 := by linarith only [lgt]
      positivity
    intro; dsimp [g]; positivity
-- Conversely, we need to show that if $l≤1$, all sequences $a_i$ in question is bounded
  intro lle a apos asucc
-- Denote the maximum of $a_i$ when $i< m$ by $M$
  have Maux : (image a (range m)).Nonempty := by
    use a 0; simp; use 0; simp; positivity
  let M := (image a (range m)).max' Maux
  have hM : ∀ i < m, a i ≤ M := by
    intro i hi; apply le_max'; simp; use i
  rw [bddAbove_iff_exists_ge 0]; use M
  simp; constructor
  · specialize apos 0; specialize hM 0 (by positivity)
    linarith only [apos, hM]
-- Use the strong induction on $i$ to prove that $a_i$ is bounded by $M$
  intro i; induction i using Nat.strong_induction_on with
  | h i ihi =>
    by_cases hi : i < m
    · exact hM i hi
    push_neg at hi; rw [asucc i hi, div_le_iff₀]; calc
      _ ≤ 1 * ∑ i ∈ range i, a i := by
        gcongr; apply le_of_lt
        apply sum_pos; intros; apply apos
        use 0; simp; linarith only [hi, mgt]
      _ ≤ ∑ i ∈ range i, M := by
        rw [one_mul]; gcongr with j hj
        apply ihi; simp at hj; exact hj
      _ = _ := by simp; ring
    norm_cast; linarith only [hi, mgt]