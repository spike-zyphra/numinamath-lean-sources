import Mathlib

/- Let $\mathbb{Z}_{>0}$ be the set of positive integers. Find all functions $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ such that  $$ m^{2}+f(n) \mid m f(m)+n $$  for all positive integers $m$ and $n$.  (Malaysia)  Answer. $f(n)=n$. -/
theorem number_theory_24372 {f : ℕ+ → ℕ+} :
  (∀ m n, m ^ 2 + f n ∣ m * f m + n) ↔ (∀ n, f n = n) := by

  constructor
  ·
    intro hf

    -- settming m = n = 2 tells us that 4 + f(2) ∣ 2f(2) + 2
    have h1 := hf 2 2
    -- since 2f(2) + 2 < 2(4 + f(2))
    have h2 : 2 * f 2 + 2 < 2 * (4 + f 2) := by
      rw [mul_add]
      nth_rw 2 [add_comm]
      refine add_lt_add_left ?bc (2 * f 2)
      norm_num
    -- we must have 2f(2) + 2 = 4 + f(2)
    have : 2 * f 2 + 2 = 4 + f 2 := by
      have ⟨k, hk⟩ := h1
      rw [hk, show 2 ^ 2 = (4 : ℕ+) by norm_cast, mul_comm] at h2
      have : k < 2 := by exact lt_of_mul_lt_mul_right' h2
      have : k = 1 := by exact PNat.eq_one_of_lt_two this
      rw [this, mul_one, show 2 ^ 2 = (4 : ℕ+) by norm_cast] at hk
      exact hk
    -- so f(2) = 2
    have hf_2 : f 2 = 2 := by
      have : (2 * f 2 + 2 : ℤ) = 4 + f 2 := by norm_cast
      have : (f 2 : ℤ) = 2 := by linear_combination' this
      norm_cast at this

    -- plugging in m = 2 then tells us 4 + f(n) ∣ 4 + n
    have h3 := hf 2
    -- which implies f(n) ≤ n for all n
    have hf_le : ∀ n, f n ≤ n := by
      intro n
      have h4 := h3 n
      rw [show 2 ^ 2 = (4 : ℕ+) by norm_cast] at h4
      rw [hf_2, show 2 * 2 = (4 : ℕ+) by norm_cast] at h4
      have h4' : (4 + f n : ℕ) ∣ 4 + n := by
        have ⟨k, hk⟩ := h4
        use k
        norm_cast
      have h_pos: (4 + n : ℕ) > 0 := by norm_cast; exact PNat.pos (4 + n)
      have := Nat.le_of_dvd h_pos h4'
      have : f n ≤ (n : ℕ) := by exact Nat.le_of_add_le_add_left this
      exact this

    -- setting m = n gives n^2 + f(n) ∣ nf(n) + n
    have h5 : ∀ n, n ^ 2 + f n ∣ n * f n + n := by
      intro n
      exact hf n n
    -- so nf(n) + n ≥ n^2 + f(n)
    have h6 : ∀ n, n * f n + n ≥ n ^ 2 + f n := by
      intro n
      have := h5 n
      exact PNat.le_of_dvd this
    -- which we rewrite as (n - 1)(f(n) - n) ≥ 0
    have h7 : ∀ n : ℕ+, (n - 1 : ℤ) * (f n - n) ≥ 0 := by
      intro n
      have : (n - 1 : ℤ) * (f n - n) = n * f n + n - (n ^ 2 + f n) := by ring
      rw [this]
      apply sub_nonneg.mpr
      norm_cast
      exact h6 n
    -- therefore f(n) ≥ n for all n ≥ 2
    have hf_ge' : ∀ n ≥ 2, f n ≥ n := by
      intro n hn
      have h_pos : (n - 1 : ℤ) > 0 := by
        have : (n : ℤ) ≥ 2 := by norm_cast
        linarith
      have : (f n - n : ℤ) ≥ 0 := by
        exact nonneg_of_mul_nonneg_right (h7 n) h_pos
      apply sub_nonneg.mp at this
      norm_cast at this

    -- this is trivially true for n = 1 also
    have hf_1 : f 1 ≥ 1 := by exact PNat.one_le (f 1)

    have hf_ge : ∀ n, f n ≥ n := by
      intro n
      by_cases h : n = 1
      · rw [h]; exact hf_1
      have : n ≥ 2 := by
        by_contra! h
        have : n ≤ 1 := by exact PNat.lt_add_one_iff.mp h
        have : n = 1 := by exact PNat.le_one_iff.mp this
        contradiction
      exact hf_ge' n this

    -- It follows that f(n) = n for all n
    intro n
    have : f n ≥ n := hf_ge n
    have : f n ≤ n := hf_le n
    apply le_antisymm
    assumption
    assumption

  · -- sufficiency is straightforward
    intro hf m n
    rw [hf n, hf m, pow_two]
