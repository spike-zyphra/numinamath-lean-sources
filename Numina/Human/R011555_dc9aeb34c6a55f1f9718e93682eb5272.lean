import Mathlib

open Finset

/- Lemma 1: 1 / a + 1 / (a + 1) + ... + 1 / (b - 1) ≤ (b - a) / a -/
lemma lemma_1 {a b : ℕ} (h₁ : 0 < a) (h₂ : a ≤ b) :
    ∑ i ∈ Ico a b, (1 / i : ℝ) ≤ (b - a) / a := by
  -- (b - a) / a = 1 / a + 1 / a + ... + 1 / a ((b - a) times)
  have H : ∑ i ∈ Ico a b, (1 / a : ℝ) = (b - a) / a := by
    simp [h₂, div_eq_mul_inv]
  rw [← H]
  -- Each term in the sum is less than or equal to 1 / a
  refine sum_le_sum (fun i hi => ?_)
  simp at hi ⊢
  exact inv_anti₀ (Nat.cast_pos'.mpr h₁) (Nat.cast_le.mpr hi.1)

/- Lemma 2: 1 / 849 + 1 / 850 + ... + 1 / 2022 < 1 -/
lemma lemma_2 : ∑ i ∈ Icc (849 : ℕ) 2022, (1 / i : ℝ) < 1 := by
  -- We split the sum into 6 parts, and apply lemma 1 to each part
  rw [← Nat.Ico_succ_right,
      ← Finset.sum_Ico_consecutive _ (show 849 ≤ 2000 by simp) (show 2000 ≤ 2023 by simp),
      ← Finset.sum_Ico_consecutive _ (show 849 ≤ 1600 by simp) (show 1600 ≤ 2000 by simp),
      ← Finset.sum_Ico_consecutive _ (show 849 ≤ 1200 by simp) (show 1200 ≤ 1600 by simp),
      ← Finset.sum_Ico_consecutive _ (show 849 ≤ 1000 by simp) (show 1000 ≤ 1200 by simp),
      ← Finset.sum_Ico_consecutive _ (show 849 ≤ 900 by simp) (show 900 ≤ 1000 by simp)]
  have h₁ := lemma_1 (show 0 < 849 by simp) (show 849 ≤ 900 by simp)
  have h₂ := lemma_1 (show 0 < 900 by simp) (show 900 ≤ 1000 by simp)
  have h₃ := lemma_1 (show 0 < 1000 by simp) (show 1000 ≤ 1200 by simp)
  have h₄ := lemma_1 (show 0 < 1200 by simp) (show 1200 ≤ 1600 by simp)
  have h₅ := lemma_1 (show 0 < 1600 by simp) (show 1600 ≤ 2000 by simp)
  have h₆ := lemma_1 (show 0 < 2000 by simp) (show 2000 ≤ 2023 by simp)
  simp at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  norm_num at h₁ h₂ h₃ h₄ h₅ h₆
  linear_combination h₁ + h₂ + h₃ + h₄ + h₅ + h₆

/- We definiëren een rij met $a_{1}=850$ en

$$
a_{n+1}=\frac{a_{n}^{2}}{a_{n}-1}
$$

voor $n \geq 1$. Bepaal alle waarden van $n$ waarvoor geldt dat $\left\lfloor a_{n}\right\rfloor=2024$.
Hierbij staat de entier $\lfloor a\rfloor$ van een reëel getal a voor het grootste gehele getal kleiner of gelijk aan a. -/
theorem algebra_605754 (a : ℕ → ℝ) (ha1 : a 1 = 850)
    (han : ∀ n ≥ 1, a (n + 1) = (a n)^2 / (a n - 1)) :
    {n | 1 ≤ n ∧ ⌊a n⌋ = 2024} = {1175} := by
  -- Lemma H₁ : ∀ n ≥ 1, 0 < a n - 1 ∧ a (n + 1) = a n + 1 + 1 / (a n - 1)
  have H₁ (n : ℕ) (hn : 1 ≤ n) : 0 < a n - 1 ∧ a (n + 1) = a n + 1 + 1 / (a n - 1) := by
    -- Let's proceed by induction
    induction n, hn using Nat.le_induction with
    -- Base case: n = 1, trivially true
    | base => norm_num [ha1, han]
    -- Inductive step: n → n + 1
    | succ n hn ih =>
      rcases ih with ⟨ih₁, ih₂⟩
      -- We have 0 < a (n + 1) - 1 by the recurrence relation and the positivity of 1 / (a n - 1)
      have h₁ : 0 < a (n + 1) - 1 := by
        rw [ih₂]
        linarith [show 1 < a n by linear_combination ih₁, show 0 < 1 / (a n - 1) by positivity]
      use h₁
      -- Rewrite the recurrence relation (cancel the denominator)
      rw [han _ (by simp)]
      field_simp
      ring
  -- Lemma H₂ : ∀ n ≥ 1, ∀ k, a (n + k) = a n + k + ∑ i ∈ Ico n (n + k), 1 / (a i - 1)
  have H₂ (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
      a (n + k) = a n + k + ∑ i ∈ Ico n (n + k), 1 / (a i - 1) := by
    -- Let's induct on k
    induction k with
    -- Base case: k = 0, trivially true
    | zero => simp
    -- Inductive step: k → k + 1
    | succ k ih =>
      -- Rewrite the hypothesis
      replace ih : ∑ i ∈ Ico n (n + k), 1 / (a i - 1) = a (n + k) - a n - k := by linear_combination -ih
      -- Simplify using the inductive hypothesis
      simp [-one_div, show n + (k + 1) = n + k + 1 by ring, Finset.sum_Ico_succ_top, ih, (H₁ (n + k) (Nat.le_add_right_of_le hn)).2]
      -- Ring identity
      ring
  -- Lemma H₃ : ∀ n ≥ 1, ∀ k, a n + k ≤ a (n + k)
  have H₃ (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
      a n + k ≤ a (n + k) := by
    -- Clearly from H₂
    specialize H₂ n hn k
    -- We have 0 ≤ ∑ i ∈ Ico n (n + k), 1 / (a i - 1) by the positivity of 1 / (a i - 1)
    suffices 0 ≤ ∑ i ∈ Ico n (n + k), 1 / (a i - 1) by linear_combination this - H₂
    refine sum_nonneg (fun x hx => ?_)
    simp at hx
    have h₁ := (H₁ x (hn.trans hx.1)).1
    positivity
  -- Lemma H₄ : ∀ n ≥ 1, 849 + n ≤ a n
  -- It is a special case of H₃
  have H₄ (n : ℕ) (hn : 1 ≤ n) : 849 + n ≤ a n := by
    specialize H₃ 1 (by simp) (n - 1)
    simp [hn, ha1] at H₃
    linear_combination H₃
  -- Lemma H₅ : 2024 ≤ a 1175
  -- It is a special case of H₄
  have H₅ : 2024 ≤ a 1175 := by
    linear_combination H₄ 1175 (by simp)
  -- Lemma H₆ : a 1175 < 2025
  have H₆ : a 1175 < 2025 := by
    rw [H₂ 1 (by simp) 1174, ha1]
    -- We only need to deal with the sum ∑ i ∈ Ico 1 (1 + 1174), (1 / (a i - 1) : ℝ)
    suffices ∑ i ∈ Ico 1 (1 + 1174), (1 / (a i - 1) : ℝ) < 1 by linear_combination this
    calc ∑ i ∈ Ico 1 (1 + 1174), (1 / (a i - 1) : ℝ)
      _ ≤ ∑ i ∈ Ico 1 (1175 : ℕ), (1 / (i + 848 : ℕ) : ℝ) := by
        -- Use the fact that 849 + n ≤ a n for all n ≥ 1
        refine sum_le_sum (fun i hi => ?_)
        simp at hi ⊢
        apply inv_anti₀ (by positivity)
        linear_combination H₄ i hi.1
      -- Rewrite the sum
      _ = ∑ i ∈ Ico (1 + 848) (1175 + 848 : ℕ), (1 / i : ℝ) := Finset.sum_Ico_add' (fun (i : ℕ) => (1 / i : ℝ)) 1 1175 848
      -- Apply lemma 2
      _ < 1 := lemma_2
  ext n
  constructor
  swap
  . -- Direction ⇐:
    -- From H₅ and H₆
    rintro rfl
    simp [Int.floor_eq_iff]
    exact ⟨H₅, by norm_num [H₆]⟩
  . -- Direction ⇒:
    -- We show that n = 1175 is the only solution
    -- It follows from the fact that the difference between consecutive terms is at least 1
    simp [Int.floor_eq_iff]
    intro hn h₁ h₂
    -- If n ≠ 1175 is a solution
    by_contra! hn₂
    rcases lt_or_gt_of_ne hn₂ with hn₃ | hn₃
    . -- Case 1: n < 1175
      -- By lemma H₃, we have a n + (1175 - n) ≤ a (n + (1175 - n)) = a 1175
      specialize H₃ n hn (1175 - n)
      simp [le_of_lt hn₃] at H₃
      -- We have n ≤ 1174
      replace hn₃ : (n : ℝ) ≤ 1174 := Nat.cast_le_ofNat.mpr (Nat.le_of_lt_succ hn₃)
      -- There is a contradiction from linear arithmetic
      linarith
    . -- Case 2: n > 1175
      -- By lemma H₃, we have a 1175 + (n - 1175) ≤ a (1175 + (n - 1175)) = a n
      specialize H₃ 1175 (by simp) (n - 1175)
      simp [le_of_lt hn₃] at H₃
      -- We have n ≥ 1176
      replace hn₃ : 1176 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn₃
      -- There is a contradiction from linear arithmetic
      linarith