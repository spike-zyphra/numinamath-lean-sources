import Mathlib

open Real Finset

/- We prove that if ∑ i, (x i) ^ 2 = 1, and ∀ i, e i ∈ [0, k-1], then ∑ i, e i * |x i| ∈ [0, (k - 1)√n] -/
lemma linear_combintion_subset_Icc_of_bounded_coeff {k : ℕ} {e : Fin n → Ico (0 : ℤ) k} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (hk : k > 1) :
    ∑ i, e i * |x i| ∈ Set.Icc 0 ((k - 1) * √n) := by
  simp
  have he_nonneg : ∀ i, 0 ≤ (e i : ℝ) := by
    intro i
    obtain h := (e i).2
    simp only [mem_Ico] at h
    simp [h.1]
  have he_bounded : ∀ i, (e i : ℝ) ≤ k - 1 := by
    intro i
    obtain h := (e i).2
    simp only [mem_Ico] at h
    norm_cast
    rw [Int.subNatNat_eq_coe, Nat.cast_one]
    apply Int.le_sub_one_of_lt
    simp [h.2]
  have hmul_nonneg : 0 ≤ ∑ i : Fin n, ↑↑(e i) * |x i| := by
    -- The sum is non-negative since e_i are non-negative and x_i^2 are non-negative.
    apply sum_nonneg
    intro i _
    apply mul_nonneg
    · apply he_nonneg
    · positivity
  use hmul_nonneg
  -- It suffices to prove that (∑ i, e i * (x i)) ^ 2 ≤ (k - 1) * n by applying the Cauchy-Schwarz inequality.
  suffices h : (∑ i, e i * |x i|) ^ 2 ≤ ((k - 1) * √n) ^ 2
  · apply pow_le_pow_iff_left₀ ?_ ?_ ?_ |>.mp h
    · exact hmul_nonneg
    · apply mul_nonneg
      · simp
        apply le_of_lt hk
      · positivity
    · simp
  · let f := fun i => (e i : ℝ) ^ 2
    let g := x ^ 2
    let r := fun i => (e i : ℝ) * |x i|
    have hf : ∀ i ∈ univ, 0 ≤ f i := by
      intro i _
      simp [f]
      positivity
    let hg : ∀ i ∈ univ, 0 ≤ g i := by
      intro i _
      simp [g]
      positivity
    let hr : ∀ i ∈ univ, r i ^ 2 = f i * g i := by
      simp [f, g, r, mul_pow]
    have hsum := sum_sq_le_sum_mul_sum_of_sq_eq_mul univ hf hg hr
    simp [f, g, r, hx] at hsum
    apply le_trans hsum
    trans ∑ _ : Fin n, (k - 1) ^ 2
    · apply sum_le_sum
      intro i _
      gcongr
      · apply he_nonneg
      · apply he_bounded
    · apply le_of_eq
      rw [mul_pow, sq_sqrt]
      · simp
        ring
      · positivity

/- Given two real numbers in the same interval [a, b], we prove that their difference is bounded by |b - a| -/
lemma abs_sub_le_of_mem_Icc {a b c d : ℝ} (h₁ : c ∈ Set.Icc a b) (h₂ : d ∈ Set.Icc a b) :
    |c - d| ≤ b - a := by
  simp at h₁ h₂
  simp [abs]
  constructor
  · trans b
    · exact h₁.2
    · rw [sub_add]
      simp [h₂.1]
  · trans b
    · exact h₂.2
    · rw [sub_add]
      simp [h₁.1]

/- 15. (FRG 2) $)^{\mathrm{IMO} 3}$ Suppose $x_{1}, x_{2}, \ldots, x_{n}$ are real numbers
  with $x_{1}^{2}+x_{2}^{2}+$ $\cdots+x_{n}^{2}=1$. Prove that for any integer $k>1$ there are integers
 $e_{i}$ not all 0 and with $\left|e_{i}\right|< k$ such that $$ \left|e_{1} x_{1}+e_{2} x_{2}+\cdots+e_{n} x_{n}\right|
  \leq \frac{(k-1) \sqrt{n}}{k^{n}-1} $$ -/
theorem algebra_24068 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (h : ∑ i : Fin n, (x i) ^ 2 = 1) (k : ℕ) (hk : 1 < k) :
    ∃ e : Fin n → ℤ,
      (∀ i : Fin n, |e i| < k) ∧
      (∃ i : Fin n, e i ≠ 0) ∧
      |∑ i : Fin n, e i * x i| ≤ ((k - 1) * √n) / (k ^ n - 1) := by
  have hone_lt_k_pow_n : 1 < k ^ n := by
    rw [show 1 = 1 ^ n by simp]
    apply Nat.pow_lt_pow_left hk
    exact Nat.not_eq_zero_of_lt hn
  -- Given, e, let eval e be the evaluation of the linear combination ∑ i, e_i * x_i.
  let eval (e : Fin n → Ico (0 : ℤ) ↑k) : ℝ := ∑ i : Fin n, e i * |x i|
  -- There are k ^ n possible choices for e, each e_i can take values in [0, k - 1].
  let s : Finset (Fin n → Ico (0 : ℤ) ↑k) := univ
  -- The image of eval must be a subset of the interval [0, (k-1)*√n].
  have himage_mem {e : Fin n → Ico (0 : ℤ) ↑k} : eval e ∈ Set.Icc 0 ((k - 1) * √n) := by
    apply linear_combintion_subset_Icc_of_bounded_coeff h hk
  simp at himage_mem
  -- We divide the interval into k ^ n - 1 subintervals of equal length $(k-1)√n /(k^n-1)$.
  let δ := (k - 1) * √n / (k ^ n - 1)
  have hδ_pos : 0 < δ := by
    simp [δ]
    apply div_pos
    · apply mul_pos
      · simp [hk]
      · simp
        exact hn
    · simp
      norm_cast
  have hdiv {e : Fin n → Ico (0 : ℤ) k} : ⌈(eval e) / δ⌉₊ ≤ k ^ n - 1 := by
    apply Nat.ceil_le.mpr
    apply div_le_iff₀ ?_ |>.mpr
    · have : k ^ n - 1 > (0 : ℝ) := by
        simp
        norm_cast
      field_simp [δ]
      apply himage_mem.2
    · exact hδ_pos
  have hdiv' {e : Fin n → Ico (0 : ℤ) k} : ⌈(eval e) / δ⌉₊ - 1 < k ^ n - 1 := by
    by_cases h : ⌈(eval e) / δ⌉₊ = 0
    · simp [h]
      norm_cast
    · apply Nat.sub_one_lt_of_le
      · exact Nat.zero_lt_of_ne_zero h
      · apply hdiv
  let divide (e : Fin n → Ico (0 : ℤ) ↑k) : Fin (k ^ n - 1) := ⟨⌈(eval e) / δ⌉₊ - 1, hdiv'⟩
  have hmem_Icc (e : Fin n → Ico (0 : ℤ) ↑k) : eval e ∈ Set.Icc (divide e * δ) ((divide e + 1) * δ) := by
    apply Set.mem_Icc.mpr
    constructor
    · apply le_div_iff₀ ?_ |>.mp
      · by_cases h : divide e = ⟨0, by simp [hone_lt_k_pow_n]⟩
        · rw [h]
          simp
          apply div_nonneg
          · apply himage_mem.1
          · apply le_of_lt hδ_pos
        · simp
          rw [Nat.cast_sub]
          · simp
            apply le_of_lt
            apply Nat.ceil_lt_add_one
            apply div_nonneg
            · apply himage_mem.1
            · positivity
          · simp [divide] at h
            apply Nat.pos_of_ne_zero at h
            simp at h
            apply le_of_lt h
      · apply hδ_pos
    · apply div_le_iff₀ ?_ |>.mp
      · simp [divide]
        by_cases h : ⌈eval e / δ⌉₊ ≥ 1
        · norm_cast
          rw [Nat.sub_add_cancel h]
          apply Nat.le_ceil
        · push_neg at h
          apply Nat.lt_one_iff.mp at h
          apply le_trans (Nat.le_ceil _)
          simp [h]
      · exact hδ_pos
  -- Note that k ^ n > k ^ n - 1, so we obtain two distinct elements e₁ e₂ such that e₁ e₂ are in the same subinterval
  let t : Finset (Fin (k ^ n - 1)) := univ
  have hcard : s.card > t.card * 1 := by
    simp [s, t]
    positivity
  have hmap : ∀ e ∈ s, divide e ∈ t := by simp [t]
  obtain ⟨y, ht, hlt⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap hcard
  obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := one_lt_card.mp hlt
  simp at h₁ h₂
  obtain he₁_mem := hmem_Icc e₁
  obtain he₂_mem := hmem_Icc e₂
  rw [h₁.2] at he₁_mem
  rw [h₂.2] at he₂_mem
  -- let e = (e₁ - e₂) * sgn(x), then e is the linear combination we are looking for.
  let e (i : Fin n) : ℤ := ((e₁ i).1 - (e₂ i).1) * (if x i ≥ 0 then 1 else -1)
  -- Note that e i * x i = (e₁ i).1 * |x i| - (e₂ i).1 * |x i|.
  have he (i : Fin n) : e i * x i = (e₁ i).1 * |x i| - (e₂ i).1 * |x i| := by
    simp [e]
    split_ifs
    · rw [abs_of_nonneg]
      · ring
      · assumption
    · rw [abs_of_neg]
      · ring
      · linarith
  use e
  split_ands
  · -- Since (e₁ i) and (e₂ i) are in [0, k-1], we have |e i| < k.
    intro i
    simp [e]
    apply lt_of_le_of_lt (b := |↑(e₁ i).1 - ↑(e₂ i).1|)
    · by_cases h : x i ≥ 0
      · simp [h]
      · simp [h]
        apply le_of_eq
        rw [abs_sub_comm]
    have h₁ : ↑(e₁ i).1 ∈ Set.Icc (0 : ℝ) (k - 1) := by
      obtain h := (e₁ i).2
      simp only [mem_Ico] at h
      simp [h.1]
      norm_cast
      rw [Int.subNatNat_eq_coe, Nat.cast_one]
      apply Int.le_sub_one_of_lt h.2
    have h₂ : ↑(e₂ i).1 ∈ Set.Icc (0 : ℝ) (k - 1) := by
      obtain h := (e₂ i).2
      simp only [mem_Ico] at h
      simp [h.1]
      norm_cast
      rw [Int.subNatNat_eq_coe, Nat.cast_one]
      apply Int.le_sub_one_of_lt h.2
    obtain h := abs_sub_le_of_mem_Icc h₁ h₂
    norm_cast at h
    simp at h
    apply lt_of_le_of_lt h
    rw [Int.subNatNat_eq_coe, Nat.cast_one]
    apply sub_one_lt
  · -- Since e₁ ≠ e₂, we have e ≠ 0
    by_contra h
    simp [e] at h
    have : e₁ = e₂ := by
      ext i
      obtain h := h i
      by_cases hx : x i ≥ 0
      · simp [hx] at h
        apply sub_eq_zero.mp h
      · simp [hx] at h
        symm
        apply sub_eq_zero.mp h
    contradiction
  · -- Note that |∑ i, e i * x i| = |eval e₁ - eval e₂|
    -- By the lemma, we have |eval e₁ - eval e₂| ≤ δ
    obtain h := abs_sub_le_of_mem_Icc he₁_mem he₂_mem
    apply le_trans ?_ (le_of_le_of_eq h ?_)
    · simp [he]
    · ring
