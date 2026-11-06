import Mathlib
/-How many two-digit positive integers are congruent to 1 (mod 3)?-/
theorem number_theory_12355 : Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n ≡ 1 [MOD 3]} = 30 := by
    --If an integer is congruent to 1 mod 3, then it can be written in the form $3k+1$. Therefore, we have two inequalities: $3k+1 \ge 10$, and $3k+1 \le 99$. The inequality $3k+1 \ge 10$ has solution $k\ge3$, and the inequality $3k+1 \le 99$ has solution $k \le 32 \frac{2}{3}$. Therefore, $k$ must be an integer between $3$ and $32$. There are $\boxed{30}$ such integers.
    apply Set.ncard_eq_of_bijective (f := fun i _ => 3 * i + 10)
    simp
    intro n h1 h2 h3
    use (n - 10) / 3
    constructor
    .
      omega
    .
      zify [h1]
      have : (3 : ℤ) ∣ n - 10 := by
        rw [← Int.natCast_modEq_iff, Nat.cast_one] at h3
        rw [← Int.modEq_iff_dvd]
        refine Int.ModEq.trans ?_ h3.symm
        simp [Int.ModEq]
      qify [this]
      ring
    .
      simp [Nat.ModEq]
      omega
    .
      omega