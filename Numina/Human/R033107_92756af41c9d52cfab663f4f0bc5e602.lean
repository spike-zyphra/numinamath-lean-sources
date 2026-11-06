import Mathlib

open Finset Real

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers, and let $S_{k}$ be the sum of products of $a_{1}, a_{2}, \ldots, a_{n}$ taken $k$ at a time.
Show that

$$
S_{k} S_{n-k} \geq\binom{ n}{k}^{2} a_{1} a_{2} \ldots a_{n}, \quad \text { for } \quad k=1,2, \ldots, n-1
$$ -/
theorem inequalities_604264 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (S : ℕ → ℝ)
    (hS : ∀ k ∈ Icc 1 n, S k = ∑ s : Finset (Icc 1 n), if s.card = k then (∏ i ∈ s, a i) else 0) :
    ∀ k ∈ Icc 1 (n - 1), S k * S (n - k) ≥ Nat.choose n k ^ 2 * ∏ i ∈ Icc 1 n, a i := by

  -- A = a₁...aₙ
  let A := ∏ i ∈ Icc 1 n, a i

  -- some properties
  -- A > 0
  have hApos : A > 0 := by
    simp [A]
    apply prod_pos
    intro i hi
    exact ha i hi
  -- production is positive
  have hprod_pos {s : Finset (Icc 1 n)} : ∏ i ∈ s, a ↑i > 0 := by
    apply prod_pos
    intro ⟨i, hi⟩ _
    simp
    exact ha i hi
  -- production is not 0
  have hprod_ne {s : Finset (Icc 1 n)} : ∏ i ∈ s, a i ≠ 0 := by
    apply ne_of_gt
    exact hprod_pos
  -- production is non-negative
  have hprod_nonneg {s : Finset (Icc 1 n)} : ∏ i ∈ s, a i ≥ 0 := by exact le_of_lt hprod_pos

  -- ∀ k, S k ≥ 0
  have hSnonneg {k : ℕ} (hk : k ∈ Icc 1 n) : S k ≥ 0 := by
    simp [hS k hk]
    apply sum_nonneg
    intro i _
    split_ifs
    · exact hprod_nonneg
    · rfl

  -- if k ∈ [1, n-1], then n-k ∈ [1, n]
  have hkmem {k : ℕ} (hk : k ∈ Icc 1 (n - 1)) : n - k ∈ Icc 1 n := by
    simp at hk ⊢
    calc
      1 = n - (n - 1) := by rw [Nat.sub_sub_self]; exact hn
      _ ≤ n - k := by rel [hk.2]

  -- if k ∈ [1, n-1], then k ∈ [1, n]
  have hkmem' {k : ℕ} (hk : k ∈ Icc 1 (n - 1)) : k ∈ Icc 1 n := by
    simp at hk ⊢
    constructor
    · exact hk.1
    · apply le_trans hk.2
      simp

  -- A = ∏ i∈s, a i * ∏ i ∈ sᶜ, a i
  have hAmul {s : Finset (Icc 1 n)} : (∏ i ∈ s, a ↑i) * (∏ i ∈ univ \ s, a i) = A := by
    simp only [A]
    rw [←Finset.prod_union]
    · have : s ∪ univ \ s = univ := by
        simp only [union_sdiff_self_eq_union]
        refine union_eq_right.mpr ?_
        exact subset_univ s
      rw [this]
      let g (x : { x // x ∈ Icc 1 n }) : ℕ := x.val
      have hg : image g univ = Icc 1 n := by simp [g]
      rw [←hg, prod_image, hg]
      simp [g]
    · exact disjoint_sdiff

  -- we show that S(n-k)=∑_{|s|=k} A/(∏ i ∈ s, a i)
  have heq {k : ℕ} (hk : k ∈ Icc 1 (n - 1)) : S (n - k) = ∑ s : Finset (Icc 1 n), if s.card = k then (A / ∏ i ∈ s, a i) else 0 := by
    simp [hS (n - k) (hkmem hk)]
    -- by constructing a bijective s ↦ sᶜ
    let e (s : Finset (Icc 1 n)) : Finset (Icc 1 n) := univ \ s
    apply sum_bijective e
    · constructor
      · intro s₁ s₂ heq
        simp only [e] at heq
        simp only [sdiff_eq_sdiff_iff_inter_eq_inter, univ_inter] at heq
        exact heq
      · intro s
        use univ \ s
        simp only [e]
        refine Finset.sdiff_sdiff_eq_self ?_
        exact subset_univ s
    · simp [e]
    · -- show that ∏ i ∈ sᶜ, a i = A / ∏ i ∈ s, a i
      intro i _
      simp only [e]
      by_cases hi : #i = n - k
      · have : #(univ \ i) = k := by
          rw [card_sdiff]
          · simp [hi]
            simp at hk
            rw [Nat.sub_sub_self]
            apply le_trans hk.2
            simp
          · exact subset_univ i
        simp only [if_pos hi, if_pos this]
        symm
        apply div_eq_of_eq_mul
        · apply hprod_ne
        · rw [hAmul]
      · have : #(univ \ i) ≠ k := by
          rw [card_sdiff]
          · simp
            by_contra h
            apply hi.elim
            rw [←h, Nat.sub_sub_self]
            have : i ⊆ univ := by exact subset_univ i
            apply card_le_card at this
            apply le_trans this
            simp
          · exact subset_univ i
        simp only [if_neg hi, if_neg this]

  -- apply the Cauchy-Schwarz inequality
  have hge {k : ℕ} (hk : k ∈ Icc 1 (n - 1)) : √(S k) * √(S (n - k)) ≥ Nat.choose n k * √A := by
    calc
      _ = √(∑ s : Finset (Icc 1 n), if s.card = k then (∏ i ∈ s, a i) else 0) * √(∑ s : Finset (Icc 1 n), if s.card = k then (A / ∏ i ∈ s, a i) else 0) := by
        -- rewrite S(n-k)=∑_{|s|=k} A/(∏ i ∈ s, a i)
        rw [heq hk, hS]
        exact hkmem' hk
      _ ≥ ∑ s : Finset (Icc 1 n), √(if s.card = k then (∏ i ∈ s, a i) else 0) * √(if s.card = k then (A / ∏ i ∈ s, a i) else 0) := by
        -- Cauchy-Schwarz inequality:  √(∑_{|s|=k}∏ i ∈ s, a i) * √(∑_{|s|=k} A/(∏ i ∈ s, a i)) ≥ ∑_{|s|=k} √(∏ i ∈ s, a i * (A/(∏ i ∈ s, a i)))
        apply Real.sum_sqrt_mul_sqrt_le
        · intro i
          split_ifs
          · exact hprod_nonneg
          · rfl
        · intro i
          split_ifs
          · apply div_nonneg
            · exact le_of_lt hApos
            · exact hprod_nonneg
          · rfl
      _ = ∑ s : Finset (Icc 1 n), (if s.card = k then √A else 0) := by
        -- show that ∏ i ∈ s, a i * (A/(∏ i ∈ s, a i)) = A
        congr
        ext s
        split_ifs
        · rw [←sqrt_mul, mul_div_cancel₀]
          · exact hprod_ne
          · exact hprod_nonneg
        · simp
      _ = _:= by
        -- the result is ∑_{|s|=k}√A = √A * n.choose k
        rw [sum_ite]
        simp

  -- therefore, S(k) * S(n - k) = √S(k) * S(n - k) ^2 ≥ (√A * n.choose k) ^ 2 = (n.choose k)^2 * a₁...aₙ
  intro k hk
  calc
    _ = (√(S k) * √(S (n - k))) ^ 2 := by
      rw [mul_pow, sq_sqrt, sq_sqrt]
      · apply hSnonneg
        exact hkmem hk
      · apply hSnonneg
        exact hkmem' hk
    _ ≥ (Nat.choose n k * √A) ^ 2 := by rel [hge hk]
    _ = _ := by
      rw [mul_pow, sq_sqrt]
      exact le_of_lt hApos
