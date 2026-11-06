import Mathlib

open scoped BigOperators

/- 3. The sequence $a_{1}, a_{2}, \ldots$ is defined by the equalities


$$

a_{1}=100, \quad a_{n+1}=a_{n}+\frac{1}{a_{n}}, \quad n \in \mathbb{N}

$$


Find the integer closest to $a_{2013}$. -/
theorem algebra_207863 (a : ℕ → ℝ)
    (h₀ : a 1 = 100)
    (h₁ : ∀ n, a (n + 1) = a n + 1 / a n) :
    round (a 2013) = 118 := by
  -- Prove by induction that 0 < a n and a n ^ 2 = a 1 ^ 2 + 2 * (n - 1) + ∑ i ∈ Finset.range (n - 1), 1 / a (i + 1) ^ 2
  -- for all n > 0.
  let rec ha : (n : ℕ) → (hn : 0 < n) → 0 < a n ∧ a n ^ 2 = a 1 ^ 2 + 2 * (n - 1) + ∑ i ∈ Finset.range (n - 1), 1 / a (i + 1) ^ 2
  -- n = 0 is trivial
  | 0 => by simp
  -- n = 1 follows from a 1 = 100
  | 1 => by simp [h₀]
  -- consider n + 2
  | n + 2 => by
    intro hn
    -- the induction hypothesis holds for n + 1
    have ⟨ih_pos, ih_eq⟩ := ha (n + 1) (by omega)
    rw [h₁ (n + 1)]
    constructor
    · positivity
    -- simplify the expression using the induction hypothesis and obtain the result
    nth_rw 1 [add_pow_two, ih_eq]
    field_simp [Finset.sum_range_succ]
    ring
  -- We have
  -- a 2013 ^ 2 = a 1 ^ 2 + 2 * 2012 + ∑ i ∈ Finset.range 2012, 1 / a (i + 1) ^ 2
  --            ≥ a 1 ^ 2 + 2 * 2012 (because 1 / a (i + 1) ^ 2 ≥ 0 for all i)
  --            > 118 ^ 2
  have h1 : a 2013 ^ 2 > 118 ^ 2 := calc
    a 2013 ^ 2 = a 1 ^ 2 + 2 * 2012 + ∑ i ∈ Finset.range 2012, 1 / a (i + 1) ^ 2 := by
        rw [(ha 2013 (by norm_num)).2]
        norm_num
    _ ≥ a 1 ^ 2 + 2 * 2012 := by
        rw [←add_zero (a 1 ^ 2 + 2 * 2012)]
        simp only [add_zero, one_div, ge_iff_le, le_add_iff_nonneg_right]
        apply Finset.sum_nonneg
        intro i _
        positivity
    _ > 118 ^ 2 := by norm_num [h₀]
  -- We have
  -- a 2013 ^ 2 = a 1 ^ 2 + 2 * 2012 + ∑ i ∈ Finset.range 2012, 1 / a (i + 1) ^ 2
  --            ≤ a 1 ^ 2 + 2 * 2012 + 2012 / a 1 ^ 2 (because a (i + 1) ^ 2 ≥ a 1 ^ 2 for all i)
  --            < 118.5 ^ 2
  have h2 : a 2013 ^ 2 < 118.5 ^ 2 := calc
    a 2013 ^ 2 = a 1 ^ 2 + 2 * 2012 + ∑ i ∈ Finset.range 2012, 1 / a (i + 1) ^ 2 := by
        rw [(ha 2013 (by norm_num)).2]
        norm_num
    _ ≤ a 1 ^ 2 + 2 * 2012 + ∑ i ∈ Finset.range 2012, 1 / a 1 ^ 2 := by
        gcongr _ + ∑ i ∈ Finset.range 2012, 1 / ?_ with i hi
        nth_rw 1 [(ha (i + 1) (by omega)).2, show a 1 ^ 2 = a 1 ^ 2 + 0 + 0 by simp_rw [add_zero]]
        gcongr
        · simp
        · apply Finset.sum_nonneg
          intro i _
          positivity
    _ = a 1 ^ 2 + 2 * 2012 + 2012 / a 1 ^ 2 := by field_simp
    _ < 118.5 ^ 2 := by norm_num [h₀]
  -- We can find x such that x ∈ (-1/2, 1/2) and a 2013 = 118 + x
  have ⟨x, hx, eq⟩ : ∃ x ∈ Set.Ico (-(1 / 2)) (1 / 2), a 2013 = (118 : ℕ) + x := by
    -- take x = a 2013 - 118
    use a 2013 - 118
    refine ⟨?_, by norm_num⟩
    -- x ∈ (-1/2, 1/2) follows from the inequalities h1 and h2
    simp only [one_div, Set.mem_Ico, neg_le_sub_iff_le_add, sub_lt_iff_lt_add]
    have hpos := (ha 2013 (by norm_num)).1
    constructor
    · rw [←tsub_le_iff_right]
      trans 118
      · norm_num
      · rw [←sq_le_sq₀ (by norm_num) (le_of_lt hpos)]
        exact le_of_lt h1
    · rw [←sq_lt_sq₀ (le_of_lt hpos) (by norm_num)]
      norm_num at h2 ⊢
      exact h2
  -- round (a 2013) = round (118 + x) = 118 + round x
  rw [eq, round_nat_add]
  -- it is enough to show that round x = 0
  suffices round x = 0 by simp only [Nat.cast_ofNat, this, add_zero]
  -- round x = 0 because x ∈ (-1/2, 1/2)
  rw [round_eq_zero_iff]
  exact hx