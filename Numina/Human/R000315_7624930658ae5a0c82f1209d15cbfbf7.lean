import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Let  $a$  and  $b$  be positive integers with  $b$  odd, such that the number   $$ \frac{(a+b)^2+4a}{ab} $$   is an integer. Prove that  $a$  is a perfect square. -/
theorem number_theory_8898
    (a b : ℕ)
    (h₀ : 0 < a)
    (h₁ : Odd b)
    (h₂ : ∃ k : ℕ, (a + b)^2 + 4 * a = k * a * b) :
    IsSquare a := by
  -- Since b is odd, it cannot be zero.
  have hb : b ≠ 0 := fun h => by
    rw [h] at h₁
    have : ¬Odd 0 := by
      rw [not_odd_iff_even]
      norm_num
    contradiction
  obtain ⟨k, hk⟩ := h₂
  zify at hk
  -- Notice that a is a root of $x^2 - (kb-2b-4)x + b^2 = 0$.
  replace hk : (a : ℤ)*a - (k*b-2*b-4)*a + b ^ 2 = 0 := by linear_combination hk
  -- By Vieta's theorem, there exists u which is another root of above equation such that
  -- $a+u=kb-2b-4$ and $au=b^2$.
  obtain ⟨u, hu, add_au, mul_au⟩ := vieta_formula_quadratic hk
  -- Since au=b^2 where a,b are positive, we know u is positive.
  have hunezero : u ≠ 0 := fun h => by
    rw [h, mul_zero] at mul_au
    have : 0 ≠ (b : ℤ) ^ 2 := by positivity
    contradiction
  -- A natural number n is square iff for all prime number q, $v_q(n)$ is even.
  have isSquare_iff (n : ℕ) : IsSquare n ↔ ∀ {q : ℕ}, q.Prime → Even (padicValNat q n) := by
    constructor
    . rintro ⟨k, hk⟩ q hq
      rcases eq_or_ne k 0 with hkzero | hknezero
      . rw [hkzero, mul_zero] at hk; norm_num [hk]
      rw [hk, padicValNat.mul (hp := ⟨hq⟩) hknezero hknezero]
      exact even_add_self _
    intro h
    rcases eq_or_ne n 0 with hn0 | hn0
    . norm_num [hn0]
    rw [← prod_pow_prime_padicValNat n hn0 (n + 1) (by omega)]
    apply Finset.isSquare_prod
    intro c hc
    simp at hc
    obtain ⟨r, hr⟩ := h hc.2
    use c ^ r
    rw [← pow_add]
    congr
  rw [isSquare_iff]
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  have vqa_add_vqu : padicValInt .. = padicValInt .. := congrArg (padicValInt q ·) mul_au
  rw [pow_two, padicValInt.mul (by positivity) (by positivity),
    padicValInt.mul (by positivity) (by positivity)] at vqa_add_vqu
  by_cases hqdvda : q ∣ a
  . -- If q divides both a and u, we can deduce a contradiction.
    have : ¬↑q ∣ u := fun hqdvdu => by
      zify at hqdvda
      -- It's obvious that q divies b^2.
      have : (q : ℤ) ∣ b ^ 2 := mul_au ▸ Dvd.dvd.mul_right hqdvda _
      -- Since q is prime number, we have q divides b.
      have hqdvdb : (q : ℤ) ∣ b := Int.Prime.dvd_pow' hq this
      -- Hence we can deduce that q divides 4 which means q = 2.
      have hqdvdaddau : ↑q ∣ a + u := Int.dvd_add hqdvda hqdvdu
      rw [add_au] at hqdvdaddau
      have : (q : ℤ) ∣ (k - 2) * b := Dvd.dvd.mul_left hqdvdb _
      have := Int.dvd_sub hqdvdaddau this
      ring_nf at this
      rw [Int.dvd_neg] at this
      norm_cast at this
      rw [show 4 = 2 ^ 2 by norm_num] at this
      have := Nat.Prime.dvd_of_dvd_pow hq this
      rw [Nat.prime_dvd_prime_iff_eq hq Nat.prime_two] at this
      -- But q cannot be 2, because b is odd.
      have : ¬Odd b := by
        rw [not_odd_iff_even, even_iff_two_dvd, ← this]
        assumption_mod_cast
      contradiction
    have : padicValInt q u = 0 := padicValInt.eq_zero_of_not_dvd this
    rw [this, add_zero] at vqa_add_vqu
    use padicValNat q b
    exact_mod_cast vqa_add_vqu
  have : padicValNat q a = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right
    exact hqdvda
  norm_num [this]
