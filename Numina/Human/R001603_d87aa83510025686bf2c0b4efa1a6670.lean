import Mathlib


/- floor of x + 1/2 is floor 2x - floor x.  -/
lemma l_floor_add_half {x: ℝ}:
  ⌊x + 1/2⌋ = ⌊2*x⌋ - ⌊x⌋ := by
  by_cases hx: x ≥ ⌊x⌋ + 1/2
  · have h1: ⌊x + 1/2⌋ = ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · linarith only [hx]
      · linarith only [Int.lt_floor_add_one x]
    have h2: ⌊2*x⌋ = 2 * ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]
      push_cast; constructor
      <;> linarith only [hx, Int.lt_floor_add_one x]
    rw [h1, h2]
    ring
  · push_neg at hx
    have h1: ⌊x + 1/2⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      constructor
      <;> linarith only [hx, Int.floor_le x]
    have h2: ⌊2*x⌋ = 2 * ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      push_cast; constructor
      <;> linarith only [hx, Int.floor_le x]
    rw [h1, h2]
    ring


/- 15. (GBR 1) ${ }^{\mathrm{IMO} 6}$ Let $[x]$ denote the integer part of $x$, i.e., the greatest integer not exceeding $x$. If $n$ is a positive integer, express as a simple function of $n$ the sum  $$ \left[\frac{n+1}{2}\right]+\left[\frac{n+2}{4}\right]+\cdots+\left[\frac{n+2^{i}}{2^{i+1}}\right]+\cdots $$ -/
theorem number_theory_24778 (n : ℕ) (npos : 0 < n) :
  ∑' i : ℕ, ⌊(n + 2^i : ℝ) / (2^(i + 1 : ℕ))⌋ = n := by

  -- each (n + 2^i) / 2^(i+1) can be written as n / 2^i - n / 2^(i+1)
  have h1: ∀i: ℕ, ⌊(n + 2^i : ℝ) / (2^(i + 1 : ℕ))⌋ =
    ⌊(n:ℝ) / 2^i⌋ - ⌊(n:ℝ) / 2^(i+1)⌋ := by
    intro i
    have: (n:ℝ) / 2^i = 2 * ( (n:ℝ) / 2^(i+1) ) := by
      rw [pow_succ]
      ring
    rw [this, ← l_floor_add_half, add_div]
    congr 2
    field_simp
    ring

  -- then this sum is (n - n/2) + (n/2 - n/4) + ...
  have h2 (m: ℕ): ∑ i ∈ Finset.range m, ⌊(n + 2^i : ℝ) / (2^(i + 1 : ℕ))⌋ =
    ∑ i ∈ Finset.range m, (⌊(n:ℝ) / 2^i⌋ - ⌊(n:ℝ) / 2^(i+1)⌋) := by
    apply Finset.sum_congr rfl ?_
    intro i _; apply h1 i
  simp only [Finset.sum_range_sub',
  pow_zero, div_one, Int.floor_natCast] at h2

  set f: ℕ → ℤ := (fun i => ⌊(↑n + 2 ^ i: ℝ) / 2 ^ (i + 1)⌋) with f_def
  obtain ⟨m, hm⟩: ∃ m, n < 2^m := by
    use n
    exact Nat.lt_two_pow_self

  -- and it simplifies to n, since from some terms on, it is 0.
  have h: ∀i, f (i + m) = 0 := by
    intro i
    simp only [f_def]
    rw [Int.floor_eq_zero_iff]
    constructor
    · positivity
    · suffices (n + 2^(i+m)) < 2^(i+m+1) by
        rify at this
        refine (div_lt_one ?_).mpr this
        positivity
      rw [pow_succ, mul_two]
      suffices 2^m ≤ 2^(i+m) by
        linarith only [hm, this]
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mpr (by simp)

  have h3: ∑ i ∈ Finset.range m, f i + ∑' i, f (i+m) = tsum f := by
    refine sum_add_tsum_nat_add' ?_
    use 0
    dsimp [HasSum]
    simp [h]
  have h4: ⌊(n:ℝ) / 2^m⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · apply div_nonneg
      <;> positivity
    · rw [div_lt_one (by simp)]
      norm_cast

  simp [← h3, h2, h, h4]