import Mathlib

open Finset

-- we define the sign function, which will lead to S = 2
def σ : ℕ → ℤ
  | n =>
    match n % 4 with
    | 0 => if n = 4 then -1 else 1
    | 1 => 1
    | 2 => if n = 2 then 1 else -1
    | 3 => if n = 3 then 1 else -1
    | _ => 1  -- unreachable case, but required for totality

/- Let $M$ be a positive integer. By replacing every $*$ in the expression $1 * 2 * 3 * \dots * (4M)$
with a plus or minus sign (+ or -), an arithmetic expression is formed. Let $S$ be the value of this expression.
Show that the smallest possible positive value of $S$ is 2.-/

theorem number_theory_636587 (M: ℕ) (hm: 0 < M):
  IsLeast {S: ℤ | 0 < S ∧ ∃ σ: ℕ → ℤ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ S = 1 + ∑ k ∈ Icc 2 (4 * M), σ k * k} 2 := by

  constructor

  -- the forward direction, show that 2 is achiveable using σ
  .
    simp
    use σ
    constructor
    .
      intro n
      have u: n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases u with u | u | u | u
      .
        simp [σ, u]
        omega
      .
        simp [σ, u]
      .
        simp [σ, u]
        omega
      .
        simp [σ, u]
        omega
    .
      -- prove by induction
      induction' M with n ih
      .
        norm_num at hm
      .
        by_cases r: n = 0
        .
          simp [r]
          simp [Finset.sum_Icc_succ_top]
          have g1: σ 2 = 1 := by
            simp [σ]
          have g2: σ 3 = 1 := by
            simp [σ]
          have g3: σ 4 = -1 := by
            simp [σ]
          rw [g1, g2, g3]
          norm_num
        .
          replace r: 0 < n := by omega
          have s:= r
          apply ih at r
          rw [show 4 * (n + 1) = 4 * n + 3 + 1 by ring]
          rw [Finset.sum_Icc_succ_top]
          rw [show 4 * n + 3 = 4 * n + 2 + 1 by ring]
          rw [Finset.sum_Icc_succ_top]
          rw [show 4 * n + 2 = 4 * n + 1 + 1 by ring]
          rw [Finset.sum_Icc_succ_top]
          rw [Finset.sum_Icc_succ_top]
          rw [r]
          clear r hm ih
          suffices σ (4 * n + 1) * ↑(4 * n + 1) + σ (4 * n + 1 + 1) * ↑(4 * n + 1 + 1) +
          σ (4 * n + 1 + 1 + 1) * ↑(4 * n + 1 + 1 + 1) +
          σ (4 * n + 1 + 1 + 1 + 1) * ↑(4 * n + 1 + 1 + 1 + 1) = 0 by omega
          have f1: σ (4 * n + 1) = 1 := by
            set m:= 4 * n + 1
            have u: m % 4 = 1 := by
              omega
            simp [σ, u]
          have f2: σ (4 * n + 1 + 1) = -1 := by
            set m:= 4 * n + 1 + 1
            have u: m % 4 = 2 := by
              omega
            simp [σ, u]
            omega
          have f3: σ (4 * n + 1 + 1 + 1) = -1 := by
            set m:= 4 * n + 1 + 1 + 1
            have u: m % 4 = 3 := by
              omega
            simp [σ, u]
            omega
          have f4: σ (4 * n + 1 + 1 + 1 + 1) = 1 := by
            set m:= 4 * n + 1 + 1 + 1 + 1
            have u: m % 4 = 0 := by
              omega
            simp [σ, u]
            omega
          simp [f1, f2, f3, f4]
          ring
          all_goals clear *-s; omega


  -- the backward direction, show that 2 is the lower bound
  .
    intro S
    rw [Set.mem_setOf]
    intro h
    rcases h with ⟨hs, h⟩
    obtain ⟨g, h1, h2⟩ := h

    -- it suffices to show that S is even
    suffices S ≠ 1 by
      clear *- this hs
      omega
    suffices S % 2 = 0 by
      clear *- this
      omega
    rw [h2]
    clear h2 hs
    rw [Int.add_emod]
    rw [Finset.sum_int_mod]

    -- we first eliminate the sign function by mod2
    have u: ∑ i ∈ Icc 2 (4 * M), (g i * ↑i) % 2 = ∑ i ∈ Icc 2 (4 * M), (i: ℤ) % 2 := by
      apply Finset.sum_congr (by simp)
      intro k hk
      rw [Int.mul_emod]
      suffices g k % 2 = 1 by simp [this]
      specialize h1 k
      rcases h1 with s | s
      .
        simp [s]
      .
        simp [s]
    rw [u]
    clear u h1
    simp

    -- prove by induction
    induction' M with n ih
    .
      norm_num at hm
    .
      by_cases r: n = 0
      .
        simp [r]
        simp [Finset.sum_Icc_succ_top]
      .
        replace r: 0 < n := by omega
        have s:= r
        apply ih at r
        rw [show 4 * (n + 1) = 4 * n + 3 + 1 by ring]
        rw [Finset.sum_Icc_succ_top]
        rw [show 4 * n + 3 = 4 * n + 2 + 1 by ring]
        rw [Finset.sum_Icc_succ_top]
        rw [show 4 * n + 2 = 4 * n + 1 + 1 by ring]
        rw [Finset.sum_Icc_succ_top]
        rw [Finset.sum_Icc_succ_top]
        simp
        rw [show (1: ℤ) +
    (∑ k ∈ Icc 2 (4 * n), ↑k % 2 + (4 * ↑n + 1) % 2 + (4 * ↑n + 1 + 1) % 2 + (4 * ↑n + 1 + 1 + 1) % 2 +
      (4 * ↑n + 1 + 1 + 1 + 1) % 2) =
      (1 +
    ∑ k ∈ Icc 2 (4 * n), ↑k % 2) + ((4 * ↑n + 1) % 2 + (4 * ↑n + 1 + 1) % 2 + (4 * ↑n + 1 + 1 + 1) % 2 +
      (4 * ↑n + 1 + 1 + 1 + 1) % 2) by ring]
        suffices (2: ℤ) ∣ (4 * ↑n + 1) % 2 + (4 * ↑n + 1 + 1) % 2 + (4 * ↑n + 1 + 1 + 1) % 2 +
          (4 * ↑n + 1 + 1 + 1 + 1) % 2 by
          apply dvd_add
          .
            tauto
          .
            tauto
        clear *-
        set m:= (n: ℤ)
        clear_value m
        apply Int.dvd_of_emod_eq_zero
        ring_nf
        rw [show (1 + m * 4) % 2 + (2 + m * 4) % 2 + (3 + m * 4) % 2 + (4 + m * 4) % 2 =
        ((1 + m * 4) % 2 + (3 + m * 4) % 2) + ((2 + m * 4) % 2 + (4 + m * 4) % 2) by ring]
        set p:= (1 + m * 4) % 2 + (3 + m * 4) % 2
        set q:= (2 + m * 4) % 2 + (4 + m * 4) % 2
        rw [Int.add_emod]
        suffices p % 2 = 0 ∧ q % 2 = 0 by
          simp [this]
        constructor
        .
          simp [p]
          rw [show 1 + m * 4 + (3 + m * 4) = 2 * (4 * m + 2) by ring]
          simp
        .
          simp [q]
          rw [show m * 4 + (4 + m * 4) = 2 * (4 * m + 2) by ring]
          simp

        all_goals clear *-s; omega
