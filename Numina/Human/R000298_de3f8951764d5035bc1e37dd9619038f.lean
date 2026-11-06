import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
/-Find all natural integers $n$ such that $(n^3 + 39n - 2)n! + 17\cdot 21^n + 5$ is a square.-/
theorem number_theory_8854 (n : ℕ) : (∃ m : ℕ, (n ^ 3 + 39 * n - 2) * Nat.factorial n + 17 * 21 ^ n + 5 = m ^ 2) ↔  (n = 1):= by
  constructor
  · intro h
    rcases h with ⟨m,hm⟩
    by_cases  w : n ≥ 3
    --When $n \ge 3$, we can prove that $3 \ | \ n!$.
    · have h1 : Nat.factorial n % 3 = 0 := by
        refine modEq_zero_iff_dvd.mpr ?_
        refine dvd_factorial ?_ w
        simp only [ofNat_pos]
      --And obviously $3 \ | 21$, so that $3 | 17 \cdot 21^n$
      have h2 : 17 * 21 ^ n % 3 = 0 := by
        refine modEq_zero_iff_dvd.mpr ?_
        have g1 : 3 ∣ 21 := by norm_num
        have g2 : 3 ∣ 21 ^ n := by refine dvd_pow g1 ?_ ;exact not_eq_zero_of_lt w
        exact dvd_mul_of_dvd_right g2 17
      have h3 : (n ^ 3 + 39 * n - 2) * Nat.factorial n % 3 = 0 := by
        have g1 : 3 ∣ Nat.factorial n := by exact dvd_of_mod_eq_zero h1
        have g2 : 3 ∣ (n ^ 3 + 39 * n - 2) * Nat.factorial n := by exact Dvd.dvd.mul_left g1 (n ^ 3 + 39 * n - 2)
        exact (dvd_iff_mod_eq_zero).mp g2
      --So
      --$$(n ^ 3 + 39n - 2) n! + 17 \cdot 21 ^ n + 5 \equiv 2 \ \ (mod \ 3)$$
      have x : ((n ^ 3 + 39 * n - 2) * Nat.factorial n + 17 * 21 ^ n + 5) % 3 = 2 % 3 := by
        simp[add_mod,reduceMod, mod_add_mod]
        calc
        _ = (((n ^ 3 + 39 * n - 2) * Nat.factorial n % 3 + 17 * 21 ^ n % 3)%3 + 2 % 3)%3 := by simp[add_mod]
        _ = _  := by simp[h3,h2]
      --But $m^2 \equiv 0,1 \ \ (mod \ 3)$.This leads to a contradiction.
      by_cases  t : m % 3 = 0
      · have h1 : 3 ∣ m := by exact dvd_of_mod_eq_zero t
        have h2 : m ^ 2 % 3 = 0 := by
          refine mod_eq_zero_of_dvd ?H
          refine Dvd.dvd.pow h1 ?H.x
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
        simp[← hm,x] at h2;
      · push_neg at t
        have h1 : m ^ 2 % 3 = 1 := by
          rw [pow_two, Nat.mul_mod]
          have g1 : m % 3 < 3 := by refine mod_lt m ?_;simp
          interval_cases m % 3
          · simp;exact t rfl
          · norm_num
          · norm_num
        rw[← hm,x] at h1;by_contra;simp at h1
    · push_neg at w
      interval_cases n
      · simp at hm
        by_contra
        match m with
        | _ + 5 => ring_nf at hm;omega
        --When $n=0$, $(n ^ 3 + 39n - 2) n! + 17 \cdot 21 ^ n + 5 = 22 = m^2$, that's wrong.
      · exact rfl
        --When $n=1$, $(n ^ 3 + 39n - 2) n! + 17 \cdot 21 ^ n + 5 = 400 = m^2$, so $n=1,m=2$
      · simp at hm
        simp
        by_cases  t : m % 3 = 0
        · have t1: m ^ 2 % 3 = 7670 % 3 := by rw[hm]
          have t2 : m ^ 2 % 3 = 0 := by simp[pow_two, Nat.mul_mod,t]
          simp[t1] at t2
        · push_neg at t
          have : m ^ 2 % 3 = 7670 % 3 := by rw[hm]
          have h1 : m ^ 2 % 3 = 1 := by
            rw [pow_two, Nat.mul_mod]
            have y : m % 3 < 3 := by refine mod_lt m ?_;simp
            interval_cases m % 3
            · simp;exact t rfl
            · norm_num
            · norm_num
          simp[this] at h1
        ----When $n=2$, $(n ^ 3 + 39n - 2) n! + 17 \cdot 21 ^ n + 5 = 7670 = m^2$, that's wrong because $7670 \equiv 2 (mod \ 3)$
  · intro h
    use 20
    simp[h]
    --When $n=1$, $(n ^ 3 + 39n - 2) n! + 17 \cdot 21 ^ n + 5 = 400 = m^2$, so $n=1,m=2$
    --Sum up, $n=1$.
