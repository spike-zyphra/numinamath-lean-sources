import Mathlib

lemma one_of_two_summands_lt_half_of_odd_sum {n i j: ℕ} (hn : Odd n) (hij : i + j = n) :
    i < (n : ℝ) / 2 ∨ j < (n : ℝ) / 2 := by
  by_contra! h
  obtain ⟨h1, h2⟩ := h
  rcases hn with ⟨k, rfl⟩
  push_cast at h1 h2
  -- Deriving the lower bound for i
  have hik : i ≥ k + 1 := by
    by_contra! h
    have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ h)
    linarith only [h1, this]
  -- Now deriving the lower bound for j
  have hjk : j ≥ k + 1 := by
    by_contra! h
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ h)
    linarith
  -- Now summing up the lower bounds
  omega

lemma diff_gt_half_bound {n k a : ℕ} (hn : Odd n) (hna : n ≥ a) (hnk : k < (n : ℝ) / 2) :
    n - k > a / 2 := by
  obtain ⟨m, rfl⟩ := hn
  push_cast at hnk
  have hkm : k ≤ m := by
    by_contra! h
    replace h : (k : ℝ) ≥ m + 1 := by exact_mod_cast h
    linarith only [hnk, h]
  omega

lemma diff_of_lt_half_is_pos {n k : ℕ} (hnk : k < (n : ℝ) / 2) : n - 2 * k > 0 := by
  replace hnk : k * 2 < n := by exact_mod_cast (lt_div_iff₀ (by norm_num)).mp <| hnk
  omega

lemma Set_finite (a : ℕ → ℝ) (n : ℕ) :
    {x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x}.Finite := by
  have : {x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x} =
      Set.image (fun i => a i + a (n - i)) (Finset.Icc 1 (n - 1)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨i, hi, j, hj, hij, hx⟩
      refine ⟨i, by simp only [Finset.coe_Icc, Set.mem_Icc] ; omega, ?_⟩
      rw [show n - i = j by omega, hx]
    · rintro ⟨i, hi, hx⟩
      simp only [Finset.coe_Icc, Set.mem_Icc] at hi
      refine ⟨i, by omega, n - i, by omega, by omega, hx⟩
  exact (this ▸ Set.toFinite _)

lemma Set_Nonempty (a : ℕ → ℝ) :
    ∀ n > 2017, {x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x}.Nonempty := by
  intro n hn
  use (a 1 + a (n - 1)), 1, (by norm_num), (n - 1), (by omega), by omega

lemma sSup_attained_of_odd (a : ℕ → ℝ) {n : ℕ} (hn : n > 2017) (hno : Odd n)
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x }) :
    ∃ k : ℕ, k < (n : ℝ) / 2 ∧ k > 0 ∧ a n = - (a k + a (n - k)) := by
  have : sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x } ∈
      { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x } :=
    Set.Nonempty.csSup_mem (Set_Nonempty a n hn) (Set_finite a n)
  obtain ⟨i, hi, j, hj, hij, heq⟩ := this
  obtain hi1 | hj1 := one_of_two_summands_lt_half_of_odd_sum hno hij
  · use i, hi1, hi
    rw [h n hn, ← heq]
    rw [show n - i = j by omega]
  · use j, hj1, hj
    rw [h n hn, ← heq]
    rw [show n - j = i by omega, add_comm]

noncomputable abbrev M (a : ℕ → ℝ) : ℝ := sSup (Set.image (fun n ↦ |a n|) (Set.Icc 1 4034))

/- For any `n` > 2017, `a n ≤ - (a i + a j)`. -/
lemma property1 (a : ℕ → ℝ)
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x }) :
    ∀ n > 2017, ∀ i > 0, ∀ j > 0, i + j = n → a n ≤ - (a i + a j) := by
  intro n hn i hi j hj hij
  rw [h n hn]
  simp only [gt_iff_lt, neg_add_rev, le_add_neg_iff_add_le, neg_add_le_iff_le_add]
  apply le_csSup ((Set_finite a n) |> Set.Finite.bddAbove)
  exact ⟨i, hi, j, hj, hij, rfl⟩

/- For any `n` in `[1, 4034]`, `a n ≤ M a`. -/
lemma property2 (a : ℕ → ℝ) {n : ℕ} (hn : n ∈ (Set.Icc 1 4034)) : |a n| ≤ M a := by
  have hs : BddAbove (Set.image (fun n ↦ |a n|) (Set.Icc 1 4034)) := by
    refine Set.Finite.bddAbove <| (Set.Finite.image _ ?_)
    exact Set.finite_Icc 1 4034
  exact le_csSup_of_le hs ⟨n, ⟨hn, by rfl⟩⟩ (by rfl)


lemma M_pos (a : ℕ → ℝ) : 0 ≤ M a :=
  calc
    0 ≤ |a 1| := abs_nonneg _
    _ ≤ M a := property2 a (by simp)

/- Estimate the lowerbound for `a n` when `Odd n`. -/
lemma odd_lowerbound (a : ℕ → ℝ) {n : ℕ}
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x })
    (hno : Odd n) :
    a n ≥ - (M a) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases ineq : n ≤ 4034
    · have : n ∈ Set.Icc 1 4034 := by
        simp only [Set.mem_Icc]
        exact ⟨Odd.pos hno, ineq⟩
      obtain ⟨h1, _⟩ := property2 a this |> abs_le.1
      exact h1.ge
    · obtain ⟨k, hk, hpos, eq⟩ := sSup_attained_of_odd a (by omega) hno h
      have hna : n ≥ 4035 := by omega
      have h1 := diff_gt_half_bound hno hna hk
      rw [show 4035 / 2 = 2017 by norm_num] at h1
      have hk1 := diff_of_lt_half_is_pos hk
      have h2 : a (n - k) ≤ - (a k + a (n - 2 * k)) := by
        rw [h (n - k) h1]
        simp only [gt_iff_lt, neg_add_rev, le_add_neg_iff_add_le, neg_add_le_iff_le_add]
        apply le_csSup ((Set_finite a (n - k)) |> Set.Finite.bddAbove)
        refine ⟨k, hpos, n - 2 * k, hk1, by omega, by rfl⟩
      have h3 : a (n - 2 * k) ≥ - M a := by
      -- Since `n - 2 * k` is odd, we can use the induction hypothesis
        apply ih
        · omega
        · exact Nat.Odd.sub_even (by omega) hno (by simp)
      rw [eq]
      linarith

/- Estimate the upperbound. -/
lemma upperbound (a : ℕ → ℝ)
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x }) :
    ∀ n > 0, a n ≤ 2 * (M a) := by
  intro n hn0
  by_cases hn1 : n ≤ 2017
  · have : n ∈ Set.Icc 1 4034 := by
      simp only [Set.mem_Icc]
      omega
    calc
      _ ≤ |a n| := le_abs_self (a n)
      _ ≤ M a := property2 a this
      _ ≤ 2 * (M a) := by linarith only [M_pos a]
  · replace hn1 : n > 2017 := Nat.gt_of_not_le hn1
    obtain hno | hne  := em (Odd n)
    · calc
        _ ≤ - (a 2 + a (n - 2)) := by
          apply property1 a h <;> omega
        _ ≤ 2 * M a := by
          have ineq1 : - a 2 ≤ M a := by
            calc
              _ ≤ |a 2| := neg_le_abs (a 2)
              _ ≤ M a := property2 a (by simp)
          have ineq2 : a (n - 2) ≥ -M a := by
            apply odd_lowerbound a h
            exact Nat.Odd.sub_even (by omega) hno (by simp)
          linarith only [ineq1, ineq2, M_pos a]
    · calc
        _ ≤ - (a 1 + a (n - 1)) := by
          apply property1 a h <;> omega
        _ ≤ 2 * M a := by
          have ineq1 : a 1 ≥ -M a := by
            apply odd_lowerbound a h
            simp
          have ineq2 : a (n - 1) ≥ -M a := by
            apply odd_lowerbound a h
            exact Nat.Even.sub_odd (by omega) (Nat.not_odd_iff_even.mp hne) (by simp)
          linarith only [ineq1, ineq2, M_pos a]

/- Estimate the lowerbound. -/
lemma lowerbound (a : ℕ → ℝ)
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x }) :
    ∀ n > 0, - 4 * M a ≤ a n := by
  intro n hn
  have M_pos a : 0 ≤ M a :=
    calc
      0 ≤ |a 1| := abs_nonneg _
      _ ≤ M a := property2 a (by simp)
  by_cases hn1 : n ≤ 2017
  · have : n ∈ Set.Icc 1 4034 := by
      simp only [Set.mem_Icc]
      omega
    obtain ⟨h1, _⟩ := property2 a this |> abs_le.1
    linarith only [h1, M_pos a]
  · replace hn1 : n > 2017 := Nat.gt_of_not_le hn1
    rw [h n hn1]
    simp only [neg_mul, gt_iff_lt, neg_le_neg_iff, ge_iff_le]
    apply csSup_le (Set_Nonempty a n hn1)
    rintro b ⟨i, hi, j, hj, hij, rfl⟩
    have ineq1 : a i ≤ 2 * M a := upperbound a h i hi
    have ineq2 : a j ≤ 2 * M a := upperbound a h j hj
    linarith only [ineq1, ineq2, M_pos a]

/- A sequence of real numbers $a_{1}, a_{2}, \ldots$ satisfies the relation
$$ a_{n}=-\max _{i+j=n}\left(a_{i}+a_{j}\right) \quad \text { for all } n>2017 $$
Prove that this sequence is bounded, i.e.,
there is a constant $M$ such that $\left|a_{n}\right| \leqslant M$ for all positive integers $n$. -/
theorem algebra_24920 (a : ℕ → ℝ)
    (h : ∀ n > 2017, a n = - sSup { x | ∃ i > 0, ∃ j > 0, i + j = n ∧ a i + a j = x }) :
    ∃ M, ∀ n > 0, |a n| ≤ M := by
  use 4 * M a
  intro n hn
  rw [abs_le]
  constructor
  -- Combine the lowerbound and upperbound estimates
  · linarith only [lowerbound a h n hn]
  · linarith only [upperbound a h n hn, M_pos a]
