import Mathlib

/-- Define the average of a finset of real numbers. -/
noncomputable def average (S : Finset ℝ) := (Finset.sum S id ) / S.card

/-- Define the deviation of a finset of real numbers. -/
noncomputable def deviation (S : Finset ℝ) := (∑ x ∈ S, (x ^ 2 - (average S) ^ 2)) / S.card

/-- Auxiliary lemma : the cardinality of a finset multiply the average of this
  finset less than or equal the sum of the square of element in this finset. -/
lemma aux_4219 (S : Finset ℝ) : S.card * (average S) ^ 2 ≤ ∑ x ∈ S, x ^ 2 := by
  by_cases ntri : (S.card : ℝ) ≠ 0
  · have := Finset.sum_mul_sq_le_sq_mul_sq S id (fun _ => 1)
    simp_rw [average, pow_two] at this ⊢
    rw [←mul_div_assoc]
    field_simp [ntri]
    norm_num [ntri] at this ⊢
    rw [div_le_iff (by norm_num [ntri])]
    replace ntri : 0 < (S.card : ℝ) := by
      simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero, Nat.cast_pos,
        Finset.card_pos] at ntri ⊢
      exact Finset.nonempty_iff_ne_empty.mpr ntri
    nlinarith [this, ntri]
  · simp only [ne_eq,  Decidable.not_not] at ntri
    simp [ntri]; exact Finset.sum_nonneg (fun _ _ => pow_two_nonneg _)

/-- Auxiliary lemma : if $ a < b$ and $(x-a)\cdot (x-b) \leq 0$, then
  $a \leq x$ and $x \leq b$. -/
lemma sub_mul_sub_nonpos {a b : ℝ} (h1 : a < b) (h2 : (x - a) * (x - b) ≤ 0) : a ≤ x ∧ x ≤ b := by
  contrapose! h2
  by_cases h : a = x
  · have : x < b := h ▸ h1
    have : b < x := h2 (le_of_eq h)
    linarith
  · by_cases h3 : a ≤ x
    · have h4 : b < x := h2 h3
      replace _ : a < x := by linarith
      exact mul_pos_iff.2 (Or.inl (by constructor <;> linarith))
    · replace h3 : x < a := by linarith
      have _ : x < b := by linarith
      exact mul_pos_iff.2 (Or.inr (by constructor <;> linarith))

/-- If the average of $\( x_{1}, x_{2}, \cdots, x_{10} \)$ is 6 and the standard deviation is $\( \sqrt{2} \)$, what is the possible range for the average of $\( x_{1}, x_{2}, \cdots, x_{5} \)$ ? -/
theorem statistics_4219 (h : S.card = (10 : ℝ)) (h1 : average S = 6) (h2 : deviation S = 2) (hT : T ⊆ S ∧ T.card = 5):
  6 - √2 ≤ average T  ∧ average T ≤ 6 + √2 := by
  -- Let $Y$ be set $S \setminus T$
  let Y := S \ T
  -- the cardinality of $Y$ equal $5$.
  have : Y.card = 5 := by norm_cast at h; simp [Y, Finset.card_sdiff hT.1, h, hT];
  have h3 : ∑ x ∈ S, x ^ 2 = 380 := by
    simp [deviation, h1, h, ] at h2
    field_simp at h2; linarith
  let aT := average T
  let aY := average Y
  have h4 : aT + aY = 12 := by
    have : aT * 5 + aY * 5 = 60 := by
      simp [aT, aY, average, this, hT, ←Finset.sum_union (Finset.disjoint_sdiff)]
      rw [Finset.union_eq_right.2 hT.1, show (60 : ℝ) = 6 * 10 by linarith, ←h, ←h1]
      simp [average, h]
    linarith
  replace h4 : average Y = 12 - average T := by linarith
  have h5 := aux_4219 T
  have h6 := aux_4219 Y
  simp [hT, this] at h5 h6; rw [h4] at h6
  -- Using the Cauchy-Schwarz inequality :
  have h7 : 5 * aT ^ 2 + 5 * (12 - aT) ^ 2 ≤ 380 := by
    calc
      _ ≤ ∑ x ∈ T, x ^ 2 + ∑ x ∈ Y, x ^ 2 := by linarith
      _ = _ := by simpa [←Finset.sum_union (Finset.disjoint_sdiff), Finset.union_eq_right.2 hT.1]
  have _ : aT ^ 2 - 12 * aT + 34 ≤ 0 := by linarith
  have h9 : (aT - (6 - √2)) * (aT - (6 + √2)) ≤ 0 := by
    have h9 : (aT - (6 - √2)) * (aT - (6 + √2)) = aT ^ 2 - 12 * aT + 34 := by
      ring_nf; simp; ring
    linarith
  have : 6 - √2 < 6 + √2 := by
    refine sub_right_lt_of_lt_add ?_; rw [add_assoc, lt_add_iff_pos_right]; simp
  exact sub_mul_sub_nonpos this h9
