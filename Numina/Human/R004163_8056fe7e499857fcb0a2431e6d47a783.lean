import Mathlib

/- Let $a_{0}, a_{1}, a_{2}, \ldots$ be a sequence of real numbers satisfying $a_{0}=1$ and $a_{n}=a_{\lfloor 7 n / 9\rfloor}+a_{\lfloor n / 9\rfloor}$ for $n=1,2, \ldots$ Prove that there exists a positive integer $k$ with $a_{k}<\frac{k}{2001 !}$.

(Here $\lfloor x\rfloor$ denotes the largest integer not greater than $x$.) -/
theorem number_theory_240230 (a : ℕ → ℝ) (h₀ : a 0 = 1) (h₁ : ∀ n, a n = a (Nat.floor (7 * n / 9)) + a (Nat.floor (n / 9))) : ∃ k > 0, a k < k / Nat.factorial 2001 := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := show ∃ α : ℝ, (7/9 : ℝ)^α + (1/9 : ℝ)^α = 1 ∧ 1/2 < α ∧ α < 1 by
    set f := λ(x : ℝ) ↦ (7/9 : ℝ)^x + (1/9)^x - 1 with hf₁
    have hf₂ : ∃ x, f x = 0 := by
      apply Set.mem_range.mp
      suffices Set.Icc (-1/9) 1 ⊆ Set.range f by
        apply Set.mem_of_subset_of_mem this
        simp
        linarith
      -- Prove that f is continuous
      apply IsConnected.Icc_subset
      · apply isConnected_range
        rw [hf₁]
        apply Continuous.add ?_ continuous_const
        apply Continuous.add
        exact Continuous.rpow continuous_const continuous_id (by simp)
        exact Continuous.rpow continuous_const continuous_id (by simp)
      all_goals rw [hf₁]; simp
      · use 1
        norm_num
      · use 0
        norm_num
    obtain ⟨α, hα₁⟩ := hf₂
    use α
    have hf₃ : Antitone f := by
      rw [hf₁]
      apply Antitone.add ?_ antitone_const
      apply Antitone.add
      exact Real.antitone_rpow_of_base_le_one (by linarith) (by linarith)
      exact Real.antitone_rpow_of_base_le_one (by linarith) (by linarith)
    split_ands
    · rw [hf₁] at hα₁
      simp at hα₁
      linarith
    · by_contra! hα₂
      have := hf₃ hα₂
      rw [hα₁] at this
      absurd this
      rw [hf₁]
      field_simp
      rw [←one_lt_sq_iff₀ (by positivity)]
      ring_nf
      rw [←Real.rpow_mul_natCast (by linarith), ←Real.rpow_mul_natCast (by linarith), add_assoc, ←Real.mul_rpow (by linarith) (by linarith)]
      norm_num
      suffices 1/9 < (7 / 81 : ℝ) ^ (1 / 2 : ℝ) * 2 by linarith
      apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
      ring_nf
      rw [←Real.rpow_mul_natCast (by linarith)]
      norm_num
    · by_contra! hα₂
      have := hf₃ hα₂
      rw [hα₁, hf₁] at this
      simp at this
      linarith

  obtain ⟨M, hM⟩ := show ∃M : ℝ, ∀ n ≥ 1, a n ≤ M * n^α by
    use 100
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    rw [h₁]
    norm_num
    by_cases h : n ≤ 8
    · have ha₁ : a 1 = 2 := by rw [h₁]; norm_num; linarith
      have ha₂ : a 2 = 3 := by rw [h₁]; norm_num; linarith
      have ha₃ : a 3 = 4 := by rw [h₁]; norm_num; linarith
      have ha₄ : a 4 = 5 := by rw [h₁]; norm_num; linarith
      have ha₅ : a 5 = 5 := by rw [h₁]; norm_num; linarith
      have ha₆ : a 6 = 6 := by rw [h₁]; norm_num; linarith
      have ha₇ : a 7 = 6 := by rw [h₁]; norm_num; linarith
      have ha₈ : a 8 = 7 := by rw [h₁]; norm_num; linarith
      have : 100 * √n ≤ 100 * n^α := by
        simp
        rw [Real.sqrt_eq_rpow]
        apply Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
        norm_num
        omega
      apply le_trans ?_ this
      have : 100 * 1 ≤ 100 * √n := by simp; omega
      apply le_trans ?_ this
      interval_cases n <;>
        norm_num <;>
        linarith

    suffices 100 * (((7 * n / 9 : ℕ) ^ α : ℝ) + (n / 9 : ℕ) ^ α) ≤ 100 * n^α by linarith [ih (7 * n / 9) (by omega) (by omega), ih (n / 9) (by omega) (by omega)]
    simp
    have h₂ : ((7 * n / 9 : ℕ) ^ α : ℝ) + (n / 9 : ℕ) ^ α ≤ ((7 * n / 9 : ℝ) ^ α) + (n / 9 : ℝ) ^ α := by
      suffices ((7 * n / 9 : ℕ) ^ α : ℝ) ≤ (7 * n / 9 : ℝ) ^ α ∧ (n / 9 : ℕ) ^ α ≤ (n / 9 : ℝ) ^ α by linarith
      split_ands
      · rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by linarith)]
        rw [show 7 * (n : ℝ) = (7 * n : ℕ) by norm_cast]
        set m := 7 * n with hm₁
        obtain ⟨q, r, hm₂, hr₁⟩ := show ∃ q r : ℕ, m = 9 * q + r ∧ r < 9 by
          use m / 9, m % 9
          omega
        rw [hm₂, show (9 * q + r) / 9 = q by omega]
        norm_num
        ring_nf
        linarith
      · rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by linarith)]
        obtain ⟨q, r, hn₂, hr₁⟩ := show ∃ q r : ℕ, n = 9 * q + r ∧ r < 9 by
          use n / 9, n % 9
          omega
        rw [hn₂, show (9 * q + r) / 9 = q by omega]
        norm_num
        ring_nf
        linarith
    apply le_trans h₂
    have : (7 * n / 9 : ℝ) ^ α + (n / 9 : ℝ) ^ α = n^α * ((7 / 9) ^ α + (1 / 9) ^ α) := by
      ring_nf
      rw [Real.mul_rpow, Real.mul_rpow]
      all_goals positivity
    rw [this, hα₁, mul_one]

  suffices ∃ k : ℕ, Nat.factorial 2001 * M * (k : ℝ)^α < k by
    obtain ⟨k, hk₁⟩ := this
    use k
    have hk₂ : 0 < k := by
      by_contra! hk₂
      simp at hk₂
      suffices (Nat.factorial 2001) * M * (k : ℝ) ^ α = k by linarith
      rw [hk₂]
      norm_num
      apply Or.inr
      apply Real.zero_rpow
      linarith
    use hk₂
    apply lt_of_le_of_lt (hM k (by linarith))
    rw [lt_div_iff₀ (by positivity)]
    linarith
  suffices ∃ k : ℕ, Nat.factorial 2001 * M < k^(1-α) ∧ 0 < k by
    obtain ⟨k, hk₁, hk₂⟩ := this
    use k
    rw [Real.rpow_sub, lt_div_iff₀, Real.rpow_one] at hk₁
    linarith
    apply Real.rpow_pos_of_pos
    all_goals norm_cast
  suffices ∃ k : ℝ, Nat.factorial 2001 * M < k^(1-α) ∧ 0 < k by
    obtain ⟨k, hk₁, hk₂⟩ := this
    use ⌈k⌉.natAbs
    have hk₃ : 0 < ⌈k⌉.natAbs := by
      rw [Int.natAbs_pos]
      apply ne_of_gt
      rw [Int.ceil_pos]
      linarith
    refine ⟨?_, hk₃⟩
    apply lt_of_le_of_lt' ?_ hk₁
    rw [Real.rpow_le_rpow_iff (by linarith) (by positivity) (by linarith)]
    have : (⌈k⌉.natAbs : ℝ) = ⌈k⌉ := by
      suffices ⌈k⌉.natAbs = ⌈k⌉ by
        rw [←this]
        norm_cast
        exact Nat.cast_natAbs ⌈k⌉
      apply Int.natAbs_of_nonneg
      apply Int.ceil_nonneg
      linarith
    rw [this]
    apply Int.le_ceil
  use (Nat.factorial 2001 * M + 1) ^ (1 / (1 - α))
  have h₂ : 0 < Nat.factorial 2001 * M := by
    apply mul_pos
    positivity
    specialize hM 1 (by linarith)
    rw [h₁] at hM
    norm_num at hM
    rw [h₀] at hM
    linarith
  split_ands
  · rw [←Real.rpow_mul, div_mul_cancel₀ 1 (by linarith), Real.rpow_one]
    repeat linarith
  · apply Real.rpow_pos_of_pos
    linarith
