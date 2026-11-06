import Mathlib


/- Let $c$ be a real number such that $c \ge 2$.
Prove that for any positive integer $n$, the number of positive divisors of $n$ does not exceed $c \sqrt{n}$. -/
theorem number_theory_637681 (c : ℝ) (hc : 2 ≤ c) (n : ℕ) (hn : 0 < n) :
    (Nat.divisors n).card ≤ c * √n := by
  suffices n.divisors.card ≤ 2 * √n by
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hc (by positivity)

  -- separate the divisors into two parts.
  have h1: n.divisors.card =
    ∑ i ∈ Finset.filter (· ≤ Nat.sqrt n) (n.divisors), 1 +
    ∑ i ∈ Finset.filter (¬ · ≤ Nat.sqrt n) (n.divisors), 1 := by
    have: n.divisors.card = ∑ i ∈ n.divisors, 1 := by simp
    rw [this]
    symm
    apply Finset.sum_filter_add_sum_filter_not

  -- each parts card ≤ √n
  have h2: Finset.filter (· ≤ Nat.sqrt n) (n.divisors) ⊆
    (Finset.range ((Nat.sqrt n) + 1)).erase 0 := by
    intro x
    simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq,
    Finset.mem_erase, Finset.mem_range, and_imp]
    intro hx1 _ hx2
    constructor
    · apply ne_zero_of_dvd_ne_zero hn.ne' hx1
    · exact Order.lt_add_one_iff.mpr hx2
  have h_card: ((Finset.range ((Nat.sqrt n) + 1)).erase 0).card = Nat.sqrt n := by
      rw [Finset.card_erase_of_mem (by simp)]
      simp
  replace h2: (Finset.filter (· ≤ Nat.sqrt n) (n.divisors)).card ≤ Nat.sqrt n := by
    nth_rw 3 [← h_card]
    apply Finset.card_le_card h2

  -- divisors > √n has a corresponding part < √n.
  have h3: (Finset.filter (¬ · ≤ Nat.sqrt n) (n.divisors)).card ≤
    ((Finset.range ((Nat.sqrt n) + 1)).erase 0).card := by
    let f: ℕ → ℕ := fun i => n/i
    apply Finset.card_le_card_of_injOn f ?_ ?_
    · simp only [not_le, Finset.mem_filter, Nat.mem_divisors,
      ne_eq, Finset.mem_erase, Finset.mem_range, and_imp]
      intro d d_dvd_n _ dgt
      have: n = d * (n/d) := by
        rw [Nat.mul_div_cancel' d_dvd_n]
      constructor
      <;> dsimp only [f]
      · rw [this] at hn
        refine Nat.pos_iff_ne_zero.mp ?_
        exact Nat.pos_of_mul_pos_left hn
      · change n.sqrt+1 ≤ d at dgt
        have: n < (n.sqrt+1) * (n.sqrt+1) := by
          apply Nat.succ_le_succ_sqrt
        replace: n < d * (n.sqrt+1) := by
          exact lt_mul_of_lt_mul_right this dgt
        exact Nat.div_lt_of_lt_mul this
    · rintro x1 hx1 x2 hx2 heq
      simp only [not_le, Finset.coe_filter, Nat.mem_divisors,
      ne_eq, Set.mem_setOf_eq, f] at hx1 hx2
      dsimp only [f] at heq
      suffices hh: (n / x1) * x1 = (n / x2) * x2 by
        rw [heq] at hh
        refine Nat.eq_of_mul_eq_mul_left ?_ hh
        exact (Nat.lt_div_iff_mul_lt' hx2.left.left 0).mpr hn
      rw [Nat.div_mul_cancel hx1.left.left, Nat.div_mul_cancel hx2.left.left]
  rw [h_card] at h3

  -- so they add up ≤ 2 √n, done.
  suffices 2 * n.sqrt ≤ 2 * √n by
    apply le_trans ?_ this
    norm_cast
    rw [two_mul, h1]
    simp only [not_le] at h3
    simp [add_le_add, h2, h3]
  simp only [Nat.ofNat_pos, mul_le_mul_left, Real.nat_sqrt_le_real_sqrt]