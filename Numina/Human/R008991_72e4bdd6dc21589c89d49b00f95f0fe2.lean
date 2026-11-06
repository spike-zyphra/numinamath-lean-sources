import Mathlib

/-Vind alle drietallen $(x, n, p)$ van positieve gehele getallen $x$ en $n$ en priemgetallen $p$ waarvoor geldt

$$
x^{3}+3 x+14=2 \cdot p^{n} \text {. }
$$-/
theorem number_theory_604997 (x n p : ℕ) (hx : 0 < x) (hp : Nat.Prime p) :
x ^ 3 + 3 * x + 14 = 2 * p ^ n ↔ (x, n, p) = (1, 2, 3) ∨ (x, n, p) = (3, 2, 5) := by
  have aux : 2 * x ≤ x ^ 2 + 7 := by
    rw [show 7 = 1+6 by simp, ← add_assoc]; apply Nat.le_add_right_of_le; rify
    apply two_mul_le_add_of_sq_eq_mul; any_goals positivity
    ring
  constructor
  -- Factorize the equation and apply mul_eq_mul_prime_pow to it
  · intro heq; have : x ^ 3 + 3 * x + 14 = (x + 2) * (x ^ 2 + 7 - 2 * x) := by
      zify; rw [Nat.cast_sub]; push_cast; ring; exact aux
    let heq' := heq; rw [this] at heq'; apply mul_eq_mul_prime_pow hp.prime at heq'
  -- Prove that $a$ divides $2$, therefore $a$ is $1$ or $2$
    rcases heq' with ⟨i, j, a, b, hij, hab, hai, hbj⟩; have : a ∣ 2 := by use b
    apply (Nat.prime_def.mp Nat.prime_two).right at this; rcases this with ha|ha
  -- If $a$ is $1$, then $b$ is $2$ and we can simplify the assumptions
    · simp [ha] at hab hai; simp [← hab] at hbj
      have ipos : 0 < i := by by_contra!; simp at this; simp [this] at hai
    -- Prove that $i$ is less or equal to $j$
      have ilej : i ≤ j := by
        rw [← Nat.pow_le_pow_iff_right hp.one_lt, ← mul_le_mul_left (show 0<2 by simp)]
        rw [← hai, ← hbj]; zify; rw [Nat.cast_sub aux]; push_cast
        rw [← sub_nonneg]; ring_nf; rw [show (3:ℤ)-x*4+x^2 = (3-x)*(1-x) by ring, mul_nonneg_iff]
        by_contra!; simp at this; rcases this with ⟨hl, hr⟩; by_cases hx : 3 ≤ x
        · specialize hr hx; linarith
        specialize hl (by linarith); replace hx : x = 2 := by linarith
        simp [hx] at hbj; suffices : Even 7; contradiction
        rw [hbj]; use p^j; ring
    -- Rearrange terms at hbj and plug in $x+2=p^i$ to it, then simplify
      zify at hbj; rw [Nat.cast_sub aux, show x = x+2-2 by simp, hai] at hbj
      push_cast at hbj; rw [Nat.cast_sub] at hbj; push_cast at hbj; ring_nf at hbj
      rw [add_comm, add_sub, sub_eq_iff_eq_add] at hbj; norm_cast at hbj
    -- Prove that $p^i$ divides $15$
      have ppowdvd : p ^ i ∣ 15 := by
        rw [Nat.dvd_add_iff_right (Nat.pow_dvd_pow p (show i ≤ i*2 by simp [mul_two]))]
        rw [hbj]; apply Nat.dvd_add; apply dvd_trans (Nat.pow_dvd_pow p ilej); all_goals simp
    -- Derive a contradiction if $p$ is neither $3$ or $5$
      by_cases pne : p ≠ 3 ∧ p ≠ 5
      · have : Fact p.Prime := ⟨hp⟩
        have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
        rw [padicValNat_dvd_iff_le, show 15 = 3*5 by simp, padicValNat.mul] at ppowdvd
        rw [padicValNat_primes, padicValNat_primes] at ppowdvd; linarith
        exact pne.right; exact pne.left; all_goals simp
      push_neg at pne; by_cases peq : p = 3
    -- If $p$ is $3$, prove that $x=1$ and $m=2$
      · simp [peq] at *; have : i < 2 := by
          by_contra!; suffices : 9 ∣ 15; contradiction; calc
            _ = 3^2 := by simp
            _ ∣ 3^i := Nat.pow_dvd_pow_iff_le_right'.mpr this
            _ ∣ _ := ppowdvd
        replace this : i = 1 := by linarith
        simp [this] at *; simp [hai] at *
        rw [show 18 = 2*3^2 by simp, mul_left_cancel_iff_of_pos, pow_right_inj₀] at heq
        symm; exact heq; all_goals simp
    -- If $p$ is $5$, prove that $x=3$ and $n=2$
      specialize pne peq; simp [pne] at *; have : i < 2 := by
        by_contra!; suffices : 25 ∣ 15; contradiction; calc
          _ = 5^2 := by simp
          _ ∣ 5^i := Nat.pow_dvd_pow_iff_le_right'.mpr this
          _ ∣ _ := ppowdvd
      replace this : i = 1 := by linarith
      simp [this] at *; simp [hai] at *
      rw [show 50 = 2*5^2 by simp, mul_left_cancel_iff_of_pos, pow_right_inj₀] at heq
      symm; exact heq; any_goals simp
      simp [← hai]
  -- If $a$ is $2$, then $b$ is $1$ and we can simplify assumptions.
    simp [ha] at *; simp [hab] at *
  -- Prove that $i$ is positive
    have ipos : 0 < i := by by_contra!; simp at this; simp [this] at hai; linarith
  -- Prove that $i$ is less or equal to $j$
    have ilej : i ≤ j := by
      rw [← Nat.pow_le_pow_iff_right hp.one_lt, ← mul_le_mul_left (show 0<2 by simp)]
      rw [← hai, ← hbj]; rify; rw [Nat.cast_sub aux]; push_cast
      rw [← sub_nonneg]; ring_nf; apply le_of_lt; calc
        _ < (x:ℝ) ^ 2 + (x - 5 / 2) ^ 2 + 23 / 4 := by positivity
        _ = _ := by ring
  -- Rearrange terms at hbj and plug in $x+2=p^i$ to it, then simplify
    rw [show x = x+2-2 by simp, hai] at hbj; zify at hbj; rw [Nat.cast_sub] at hbj
    push_cast at hbj; rw [Nat.cast_sub] at hbj; push_cast at hbj; ring_nf at hbj
    rw [add_comm, add_sub, sub_eq_iff_eq_add] at hbj; norm_cast at hbj
  -- Prove that $p^i$ divides $15$
    have ppowdvd : p ^ i ∣ 15 := by
      have : p ^ i ∣ p ^ j + p ^ i * 12 := by
        apply Nat.dvd_add; apply dvd_trans (Nat.pow_dvd_pow p ilej); all_goals simp
      rw [← hbj, ← Nat.dvd_add_iff_right] at this; exact this
      apply dvd_trans (Nat.pow_dvd_pow p (show i ≤ i*2 by simp [mul_two])); simp
  -- Derive a contradiction if $p$ is neither $3$ or $5$
    by_cases pne : p ≠ 3 ∧ p ≠ 5
    · have : Fact p.Prime := ⟨hp⟩
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      rw [padicValNat_dvd_iff_le, show 15 = 3*5 by simp, padicValNat.mul] at ppowdvd
      rw [padicValNat_primes, padicValNat_primes] at ppowdvd; linarith
      exact pne.right; exact pne.left; all_goals simp
    push_neg at pne; by_cases peq : p = 3
    -- Derive a contradiction if $p$ is $3$
    · simp [peq] at *; have : i < 2 := by
        by_contra!; suffices : 9 ∣ 15; contradiction; calc
          _ = 3^2 := by simp
          _ ∣ 3^i := Nat.pow_dvd_pow_iff_le_right'.mpr this
          _ ∣ _ := ppowdvd
      replace this : i = 1 := by linarith
      simp [this] at *; simp [hai] at *; suffices : 5 ∣ 3; contradiction
      replace heq : 5 ∣ 3 ^ n := by
        rw [← Nat.Coprime.dvd_mul_left (show Nat.Coprime 5 2 by norm_num), ← heq]; norm_num
      apply Nat.prime_five.dvd_of_dvd_pow heq
  -- Derive a contradiction if $p$ is $5$
    specialize pne peq; simp [pne] at *; have : i < 2 := by
      by_contra!; suffices : 25 ∣ 15; contradiction; calc
        _ = 5^2 := by simp
        _ ∣ 5^i := Nat.pow_dvd_pow_iff_le_right'.mpr this
        _ ∣ _ := ppowdvd
    replace this : i = 1 := by linarith
    simp [this] at *; simp [hai] at *  ; suffices : 11 ∣ 5; contradiction
    replace heq : 11 ∣ 5 ^ n := by
      rw [← Nat.Coprime.dvd_mul_left (show Nat.Coprime 11 2 by norm_num), ← heq]; norm_num
    apply (show Nat.Prime 11 by norm_num).dvd_of_dvd_pow heq
  -- Finish the rest trivial goals
    simp [← hai]; simp [← hai]; exact aux
-- Conversely, it is straightforward to check that the given values are solutions to the equation
  simp; intro h; rcases h with ⟨_,_,_⟩|⟨_,_,_⟩; all_goals simp_all