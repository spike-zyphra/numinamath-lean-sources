import Mathlib

def f: ℤ → ℤ := fun k => (k * (3 * k - 7)) / 2

/-Let $X$ be an integer such that $X \ge -2$. Let $f(k)$ be a function defined
for any natural number $k$ as $f(k) = \sum_{i=0}^{k-1} (3i-2)$,
where the sum is taken to be 0 if $k=0$. (This function can be written in closed form as $f(k) = \frac{k(3k-7)}{2}$).
Theorem: There exists a natural number $n$ such that $f(n) \le X \le f(n+1)$ and $f(n) \le f(n+1)$.-/

theorem number_theory_635644 (X: ℤ) (h: -2 ≤ X): ∃ n, 0 ≤ n ∧ f n ≤ X ∧ X ≤ f (n + 1) ∧ f n ≤ f (n + 1) := by

  by_cases l: X < 0

  -- case X < 0
  .
    interval_cases X
    .
      use 1
      simp [f]
    .
      use 1
      simp [f]

  -- case X ≥ 0, prove by induction
  .
    have s: ∀ m: ℕ, ∃ n, 0 ≤ n ∧ f n ≤ m ∧ m ≤ f (n + 1) ∧ f n ≤ f (n + 1) := by
      intro m
      induction m with
      | zero =>
        use 2
        simp [f]
      | succ m ih =>
        obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih
        by_cases r: m + 1 ≤ f (n + 1)
        .
          use n
          omega
        .
          use n + 1
          refine ⟨by omega, ?_⟩
          refine ⟨by omega, ?_⟩
          have o: 1 ≤ n := by
              suffices n ≠ 0 by omega
              by_contra! g
              simp [f, g] at hn3
              omega
          have x: 2 ∣ (n + 2) * (3 * (n + 2) - 7) := by
              rw [Int.dvd_iff_emod_eq_zero]
              rw [show 3 * (n + 2) - 7 = 3 * n - 1 by omega]
              rw [Int.mul_emod]
              rw [show (n + 2) % 2 = (n % 2 + 2) % 2 by rw [Int.add_emod]; simp]
              rw [show (3 * n - 1) % 2 = (n % 2 - 1) % 2 by rw [Int.sub_emod]; rw [Int.mul_emod]; simp]
              have v: n % 2 = 0 ∨ n % 2 = 1 := by omega
              rcases v with v | v
              .
                simp [v]
              .
                simp [v]
          have y: 2 ∣ (n + 1) * (3 * (n + 1) - 7) := by
              rw [Int.dvd_iff_emod_eq_zero]
              rw [show 3 * (n + 1) - 7 = 3 * n - 4 by omega]
              rw [Int.mul_emod]
              rw [show (n + 1) % 2 = (n % 2 + 1) % 2 by rw [Int.add_emod]; simp]
              rw [show (3 * n - 4) % 2 = n % 2 by rw [Int.sub_emod]; rw [Int.mul_emod]; simp]
              have v: n % 2 = 0 ∨ n % 2 = 1 := by omega
              rcases v with v | v
              .
                simp [v]
              .
                simp [v]
          constructor
          .
            rw [show n + 1 + 1 = n + 2 by ring]
            suffices f (n + 1) + 1 ≤ f (n + 2) by
              omega
            rw [f]
            rw [f]
            qify
            rw [Rat.intCast_div]
            rw [Rat.intCast_div]
            simp
            set v:= (n: ℚ)
            have lv: 1 ≤ v := by
              qify at o
              tauto
            clear * - lv
            nlinarith
            .
              tauto
            .
              tauto

          .
            rw [show n + 1 + 1 = n + 2 by ring]
            rw [f]
            rw [f]
            qify
            rw [Rat.intCast_div]
            rw [Rat.intCast_div]
            simp
            set v:= (n: ℚ)
            have lv: 1 ≤ v := by
              qify at o
              tauto
            clear * - lv
            nlinarith
            .
              tauto
            .
              tauto

    simp at l
    specialize s X.natAbs
    zify at s
    rw [show |X| = X by apply abs_of_nonneg (by omega)] at s
    tauto