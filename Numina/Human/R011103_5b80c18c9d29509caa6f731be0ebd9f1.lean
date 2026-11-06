import Mathlib

open Set

/- How many positive [integers](https://artofproblemsolving.com/wiki/index.php/Integer) $b$ have the property that $\log_{b} 729$ is a positive integer?
$\mathrm{(A) \ 0 } \qquad \mathrm{(B) \ 1 } \qquad \mathrm{(C) \ 2 } \qquad \mathrm{(D) \ 3 } \qquad \mathrm{(E) \ 4 }$ -/
-- This is a somewhat contrived way to avoid a definition of `s` outside the problem statement.
theorem number_theory_1115 (s: Set ℕ) (p: s = ({ b > 1 | ∃n: ℕ, Real.logb b 729 = n } : Set ℕ)) : ∃p: Fintype s, s.toFinset.card = 4 := by

  /- If $\log_{b} 729 = n$, then $b^n = 729$ -/
  have q {b n: ℕ} (r: 1 < b): (Real.logb b 729 = n) ↔ b^n = 729 := by
    rw [Real.logb_eq_iff_rpow_eq]
    norm_cast
    case hy => norm_num
    all_goals (norm_cast; linarith)

  -- We can already say that b > 1 by distinguishing cases
  have b_gt_one (b n: ℕ) (h: b^n = 729) : b > 1 := by
    apply by_contradiction
    intro h'
    rw [not_lt] at h'
    interval_cases b
    · cases eq_zero_or_pos n with
      | inl n_zero => simp only [n_zero, Nat.pow_eq, Nat.pow_zero 0, OfNat.one_ne_ofNat] at h
      | inr n_neZero =>
        simp [Nat.pow_eq, Nat.zero_pow n_neZero] at h
    · simp [Nat.one_pow] at h

  simp at p
  have r: s = { b | ∃n, b.pow n = 729 } := by
    rw [p]
    ext b
    rw [Set.mem_setOf, Set.mem_setOf]
    -- rw [q]
    constructor
    · intro ⟨t, n, h⟩
      rw [q t] at h
      exact ⟨n, h⟩

    · intro ⟨n, h⟩
      constructor
      · exact (b_gt_one b n h)
      · use n
        rw [q (b_gt_one b n h)]
        exact h

  -- Since $729 = 3^6$, $b$ must be $3$ to some [factor](https://artofproblemsolving.com/wiki/index.php/Factor) of 6.
  have pow_729: 729 = 3^6 := rfl
  have b_pow_three {b : ℕ} {n: ℕ} (hpow: b^n = 729) : ∃k: ℕ, k ≤ 6 ∧ b = 3^k := by
    rw [<- Nat.dvd_prime_pow (by norm_num)]
    rw [pow_729] at hpow

    induction n with
    | zero => simp [Nat.pow_zero] at hpow
    | succ n _ =>
      apply Dvd.intro (b^n)
      rw [<- Nat.pow_add_one', hpow]
  save

  have b_pow_three' (b: ℕ) : (∃n:ℕ, (b^n = 729)) ↔ ∃k: ℕ, k ∣ 6 ∧ b = 3^k := by
    constructor
    case mp =>
      intro ⟨n, h⟩
      have ⟨k, ⟨p, p'⟩⟩ := b_pow_three h
      use k
      rw [pow_729, p', <- Nat.pow_mul] at h
      apply Nat.pow_right_injective (by norm_num) at h

      exact ⟨Dvd.intro n h, p'⟩
    case mpr =>
      intro ⟨k, ⟨n, h⟩, h'⟩
      use n
      rw [h', <- Nat.pow_mul, <- h]

  -- Thus, there are four (3, 9, 27, 729) possible values of $b \Longrightarrow \boxed{\mathrm{E}}$.
  have num_list: s = ({3,9,27,729}: Finset ℕ) := by
    rw [r]
    ext b
    simp only [Set.mem_setOf, Nat.pow_eq, b_pow_three' b]

    have div_6 : Nat.divisors 6 = {1,2,3,6} := rfl
    have div_6' (k: ℕ): k ∣ 6 ↔ k ∈ ({1,2,3,6}: Finset ℕ) := by
      rw [<- div_6, Nat.mem_divisors]
      simp

    simp [div_6']

  simp [num_list]
  rw [exists_true_iff_nonempty]
  constructor
  rw [num_list]
  infer_instance