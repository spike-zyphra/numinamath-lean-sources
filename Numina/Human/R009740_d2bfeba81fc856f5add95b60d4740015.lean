import Mathlib

set_option maxRecDepth 1000

theorem other_24617 (p q : ℕ) (hpq : p < 100 ∧ q ≠ 0 ∧ q < 100) : IsLeast {x : ℝ | ∃ p q : ℕ, p < 100 ∧ q ≠ 0 ∧ q < 100 ∧ x = |p / q - Real.sqrt 2|} (|p / q - Real.sqrt 2|) ↔ (p, q) = (99, 70) := by
  -- We first show that minimal element of the set is |99 / 70 - Real.sqrt 2|.
  have h₀ : IsLeast {x : ℝ | ∃ p q : ℕ, p < 100 ∧ q ≠ 0 ∧ q < 100 ∧ x = |p / q - Real.sqrt 2|} (|99 / 70 - Real.sqrt 2|) := by
    -- First, we observe that the set does have a minimum, because p, q have only finitely many choices.
    let S := {x : ℝ | ∃ p q : ℕ, p < 100 ∧ q ≠ 0 ∧ q < 100 ∧ x = |p / q - Real.sqrt 2|}
    rw [show {x : ℝ | ∃ p q : ℕ, p < 100 ∧ q ≠ 0 ∧ q < 100 ∧ x = |p / q - Real.sqrt 2|} = S by simp only [S]]
    have h₁ : ∃ x_min : S, ∀ y : S, ¬y < x_min := by
      let U : Finset (ℕ × ℕ) := Finset.filter (fun (p, q) => p < 100 ∧ q ≠ 0 ∧ q < 100) (Finset.range 100 ×ˢ Finset.range 100)
      have h₁ : U.Nonempty := by
        simp only [Finset.Nonempty]
        use (99, 70)
        simp [U]
      let S' : Finset ℝ := Finset.image (fun (p, q) => |p / q - Real.sqrt 2|) U
      have h₂ : S = S' := by
        ext x
        simp [S, S', U]
        apply Iff.intro
        <;> intro h₂
        . obtain ⟨p, hp, q, hq, hx⟩ := h₂
          use p, q + 1
          simp [hp, hq, hx]
        . obtain ⟨p, q, ⟨⟨hp₁, hq₁⟩, ⟨_, hq₂, _⟩⟩, hx⟩ := h₂
          use p
          simp [hp₁]
          use q - 1
          rw [Nat.sub_add_cancel (by omega)]
          use hq₁
          norm_cast
          rw [Nat.sub_add_cancel (by omega), hx]
      rw [h₂]
      simp (config := { autoUnfold := false }) [-not_lt]
      apply Finset.exists_minimal
      apply Finset.Nonempty.image h₁
    replace h₁ : ∃ x_min : ℝ, x_min ∈ S ∧ ∀ y : ℝ, y ∈ S → ¬y < x_min := by
      obtain ⟨x_min, h₁⟩ := h₁
      use x_min
      simp
      intro y hy
      specialize h₁ ⟨y, hy⟩
      simp at h₁
      norm_cast
    obtain ⟨x_min, hx, h₁⟩ := h₁
    simp at h₁
    have h₂ : IsLeast S x_min := by
      simp [IsLeast, lowerBounds, hx]
      exact h₁
    simp only [S, Set.mem_setOf] at hx
    obtain ⟨p, q, hp₁, hq₁, hq₂, hx⟩ := hx
    -- Since 41 / 29 < √2 < 99 / 70, p / q must be between 41 / 29 and 99 / 70.
    have h₃ : 41 / 29 ≤ (p / q : ℝ) := by
      by_contra!
      have h₃ : 41 / 29 < Real.sqrt 2 := by
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      replace this : |p / q - Real.sqrt 2| > |41 / 29 - Real.sqrt 2| := by
        nth_rewrite 1 [<-abs_neg]
        nth_rewrite 2 [<-abs_neg]
        rw [abs_of_nonneg, abs_of_nonneg]
        linarith only [this]
        linarith only [h₃]
        linarith only [h₃, this]
      have h₄ : |41 / 29 - Real.sqrt 2| ∈ S := by
        simp only [S, Set.mem_setOf]
        use 41, 29
        simp
      specialize h₁ |41 / 29 - Real.sqrt 2| h₄
      linarith only [hx, h₁, this]
    have h₄ : (p / q : ℝ) ≤ 99 / 70 := by
      by_contra!
      have h₄ : Real.sqrt 2 < 99 / 70 := by
        rw [Real.sqrt_lt]
        all_goals
          norm_num
      replace this : |p / q - Real.sqrt 2| > |99 / 70 - Real.sqrt 2| := by
        rw [abs_of_nonneg, abs_of_nonneg]
        linarith only [this]
        linarith only [h₄]
        linarith only [h₄, this]
      have h₅ : |99 / 70 - Real.sqrt 2| ∈ S := by
        simp only [S, Set.mem_setOf]
        use 99, 70
        simp
      specialize h₁ |99 / 70 - Real.sqrt 2| h₅
      linarith only [hx, h₁, this]
    -- If 41 / 29 < p / q < 99 / 70, then since 99 * 29 - 41 * 70 = 1, we arrive at a contradiction.
    have h₅ : (p / q : ℝ) = 41 / 29 ∨ (p / q : ℝ) = 99 / 70 := by
      by_contra! h₅
      replace h₅ : 41 / 29 < (p / q : ℝ) ∧ (p / q : ℝ) < 99 / 70 := by
        refine ⟨?_, ?_⟩
        . linarith (config := { splitNe := true }) only [h₃, h₅.1]
        . linarith (config := { splitNe := true }) only [h₄, h₅.2]
      rw [div_lt_div_iff, div_lt_div_iff] at h₅
      norm_cast at h₅
      omega
      all_goals
        simp [show 0 < q by omega]
    cases h₅ with
    | inl h₅ =>
      -- Note that |41 / 29 - √2| > |99 / 70 - √2|, so this solution is discarded.
      rw [hx, h₅] at h₁
      have h₆ : |99 / 70 - Real.sqrt 2| ∈ S := by
        simp only [S, Set.mem_setOf]
        use 99, 70
        simp
      specialize h₁ |99 / 70 - Real.sqrt 2| h₆
      rw [<-abs_neg, abs_of_nonneg, abs_of_nonneg] at h₁
      replace h₁ : Real.sqrt 2 ≤ (99 / 70 + 41 / 29) / 2 := by
        linarith only [h₁]
      rw [Real.sqrt_le_iff] at h₁
      norm_num at h₁
      norm_num
      rw [Real.sqrt_le_iff]
      norm_num
      norm_num
      rw [Real.le_sqrt]
      norm_num
      norm_num
      norm_num
    | inr h₅ =>
      rw [hx, h₅] at h₂
      exact h₂
  -- Back to the main goal and break the iff into two implications.
  apply Iff.intro
  <;> intro h₁
  . -- If |p / q - √2| = |99 / 70 - √2|, then p = 99 and q = 70.
    have h₂ := IsLeast.unique h₀ h₁
    rw [<-sq_eq_sq_iff_abs_eq_abs] at h₂
    apply sub_eq_zero_of_eq at h₂
    rw [sq_sub_sq] at h₂
    simp at h₂
    cases h₂ with
    | inl h₂ =>
      simp
      replace h₂ : ((99 / 70 + p / q : ℚ) / 2 : ℚ) = Real.sqrt 2 := by
        rify
        linarith only [h₂]
      have weq : ¬Irrational (Real.sqrt 2) := by
        simp [Irrational]
        use (99 / 70 + (p / q : ℚ)) / 2
      absurd weq
      exact irrational_sqrt_two
    | inr h₂ =>
      simp at h₂ ⊢
      field_simp [hpq.2.1] at h₂ -- We used hq implicitly here.
      apply eq_of_sub_eq_zero at h₂
      norm_cast at h₂
      have h₃ : 99 ∣ 70 * p := by
        rw [<-h₂]
        apply dvd_mul_right
      rw [Nat.Coprime.dvd_mul_left (by norm_num)] at h₃
      rw [dvd_iff_exists_eq_mul_right] at h₃
      obtain ⟨p', h₃⟩ := h₃
      have h₄ : p' ≤ 1 := by
        omega
      interval_cases p'
      . simp [h₃, hpq] at h₂
      . omega
  . simp at h₁
    simp [h₁.1, h₁.2]
    simp at h₀
    exact h₀
