import Mathlib

open Complex

/-Does there exist a triangle such that the lengths of all its sides and altitudes are integers and its perimeter is equal to 1995 ?-/
theorem geometry_606416 (A B C : ℂ) (hA : A = 0) (hB : ∃ m : ℕ, 0 < m ∧ B = m)
(hC : (∃ n : ℕ, 0 < n ∧ C.abs = n) ∧ (∃ l : ℕ, 0 < l ∧ (C - B).abs = l) ∧ 0 < C.re)
(hH2 : ∃ h : ℕ, 0 < h ∧ C.im = h) :
¬ (A - B).abs + (B - C).abs + (C - A).abs = 1995 := by
-- By the assumption, we can see that $A$ is the origin, $B$ lies on the $x$-axis and $C$ lies in the upper half plane
-- Assume the contrary that the perimeter of the triange is $1995$, we first rewrite the existence assumptions by naming new variables
-- then rewrite the perimeter assumption in terms of these variables
  intro hperi; rcases hB with ⟨m, ⟨mpos, hm⟩⟩; rcases hC with ⟨⟨n, ⟨npos, hn⟩⟩, ⟨l, ⟨lpos, hl⟩⟩, hC⟩
  rcases hH2 with ⟨h, ⟨hpos, hh⟩⟩; simp [hA] at hperi; rw [← dist_eq, dist_comm, dist_eq] at hperi
  rw [hl, hm, hn] at hperi; simp at hperi; norm_cast at hperi
-- Prove that $h$ is less or equal to $n$
  have hlen : h ≤ n := by
    rw [Complex.abs_eq_sqrt_sq_add_sq, hh] at hn; apply_fun fun t => t ^ 2 at hn
    rw [Real.sq_sqrt] at hn; rify; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), ← hn]
    simp; all_goals positivity
-- Rewrite the complex absolute value in hn in terms of $h$ and take square both sides
  let hn' := hn; rw [Complex.abs_eq_sqrt_sq_add_sq, hh] at hn'; apply_fun fun t => t ^ 2 at hn'
  rw [Real.sq_sqrt, ← eq_sub_iff_add_eq, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub] at hn'
-- Rewrite the complex absolute value in hl in terms of $h$ and take square both sides
  let hl' := hl; rw [Complex.abs_eq_sqrt_sq_add_sq, hm] at hl'
  apply_fun fun t => t ^ 2 at hl'; rw [Real.sq_sqrt, ← re_add_im C, ← sub_add_eq_add_sub] at hl'
  rw [add_re, add_im, ← eq_sub_iff_add_eq, hh] at hl'; norm_cast at hl'; simp at hl'
-- Prove that $C.re$ is an integer
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C.re = k := by
  -- If $n^2-h^2$ is a square $u^2$, then u is the desired integer we want
    by_cases hsq : IsSquare (n ^ 2 - h ^ 2)
    · rcases hsq with ⟨u, hu⟩; use u; rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)]
      rw [hn', hu]; push_cast; ring; all_goals positivity
  -- If $n^2-h^2$ is not a square, then its square root is irrational. We will prove the contrary that it is rational
    rw [← irrational_sqrt_natCast_iff] at hsq; suffices : ∃ q : ℚ, √↑(n ^ 2 - h ^ 2) = q
    · rcases this with ⟨q, hq⟩; have : ¬ Irrational √↑(n ^ 2 - h ^ 2) := by
        rw [hq]; exact q.not_irrational
      contradiction
  -- Subtract hn' and hl' and solve for $C.re$
    rw [← hn', Real.sqrt_sq]; apply_fun fun t => t - (C.re - ↑m) ^ 2 at hn'; nth_rw 2 [hl'] at hn'
    rw [Nat.cast_sub] at hn'; push_cast at hn'; rw [sub_sub_sub_cancel_right] at hn'
    ring_nf at hn'; rw [sub_eq_iff_eq_add, mul_assoc, ← eq_div_iff] at hn'
    norm_cast at hn'; use Rat.divInt (Int.subNatNat (n ^ 2) (l ^ 2) + ↑(m ^ 2)) ↑(m * 2)
  -- Finish the rest trivial goals
    positivity; apply Nat.pow_le_pow_left; exact hlen; positivity
-- Rewrite hn' hl' in terms of $k$, then subtract them
  simp [hk] at hn' hl'; norm_cast at hn' hl'; zify at hn'; rw [Nat.cast_sub] at hn'
  rw [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at hl'; push_cast at hn' hl'
  apply_fun fun t => t - ((k:ℤ) - m) ^ 2 at hn'; nth_rw 2 [hl'] at hn'
  ring_nf at hn'; rw [sub_eq_sub_iff_add_eq_add] at hn'; norm_cast at hn'
-- Take mod $2$ on both sides of hn' and hperi, then check all possible cases to derive a contradiction
  apply_fun fun t => t % 2 at hperi hn'; rw [Nat.add_mod] at hperi hn'
  nth_rw 2 [Nat.add_mod] at hperi hn'; rw [Nat.mul_mod_left, zero_add, Nat.pow_mod, Nat.mod_mod] at hn'
  nth_rw 2 [Nat.pow_mod] at hn'; nth_rw 3 [Nat.pow_mod] at hn'
  have := Nat.mod_lt m (show 0<2 by simp); have := Nat.mod_lt l (show 0<2 by simp)
  have := Nat.mod_lt n (show 0<2 by simp)
  interval_cases m % 2 <;> interval_cases n % 2 <;> interval_cases l % 2
  any_goals simp_all
-- Finish the rest trivial goals
  any_goals apply Nat.pow_le_pow_left; exact hlen
  all_goals positivity