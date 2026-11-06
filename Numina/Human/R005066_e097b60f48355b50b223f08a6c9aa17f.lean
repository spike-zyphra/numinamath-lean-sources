import Mathlib

/- Find all functions $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ such that the number $x f(x)+f^{2}(y)+2 x f(y)$ is a perfect square for all positive integers $x, y$. -/
theorem number_theory_605360 (f : ℕ → ℕ) (fpos : ∀ x > 0, 0 < f x) :
(∀ x > 0, ∀ y > 0, IsSquare (x * f x + f y ^ 2 + 2 * x * f y)) ↔ ∀ x > 0, f x = x := by
  constructor
-- According to the reference answer, the key lemma in proving the theorem is the following explicit formulas for $f$ on prime numbers
  · intro hsq; have key : ∀ p, p.Prime → f p = p ∨ 4 * f p = (p - 3) ^ 2 ∨ 4 * f p =
    3 * p ^ 2 - 6 * p + 3 ∨ 4 * f p = (3 * p - 1) ^ 2 := by
    -- Plug in $x=y=p$ to hsq to obtain a square number $k^2$
      intro p ppr; obtain ⟨k, hk⟩ := hsq p ppr.pos p ppr.pos; specialize fpos p ppr.pos
      zify at hk; rw [← sub_eq_zero] at hk; apply_fun fun t => t * (4:ℤ) + 9 * p ^ 2 at hk;
    -- Factorize the LHS of hk
      rw [show ((p:ℤ)*(f p)+(f p)^2+2*p*(f p)-k*k)*4+9*p^2 = (2*f p+3*p-2*k)*(2*f p+3*p+2*k) by ring] at hk
      rw [zero_mul, zero_add] at hk; let hk' := hk; norm_cast at hk'; have := ppr.two_le
      rw [Int.subNatNat_eq_coe, ← Nat.cast_sub] at hk'; norm_cast at hk'
    -- Apply mul_eq_mul_prime_pow and discuss every possible cases of the exponents
      obtain ⟨i, j, b, c, hij, hbc, h1, h2⟩ := mul_eq_mul_prime_pow ppr.prime hk'
      have : i ≤ 2 := by omega
      have : b ∣ 3^2 := by use c; omega
      rw [Nat.dvd_prime_pow Nat.prime_three] at this; rcases this with ⟨u, ⟨ule, hu⟩⟩
      interval_cases i <;> interval_cases u
      -- In the first case, after simplifying all the assumptions, we will get $4 * f p = (3 * p - 1) ^ 2$
      · symm at hbc; simp at hu hij; simp [hu] at hbc h1; rw [hbc, hij] at h2
        apply_fun fun t => t - 1 at h2; nth_rw 1 [← h1, Nat.add_sub_sub_cancel, ← two_mul] at h2
        apply_fun fun t => 2 * t at h1; rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, h2] at h1
        rw [Nat.mul_add] at h1; symm at h1; rw [← Nat.sub_eq_iff_eq_add] at h1; ring_nf at h1
        right; right; right; rw [mul_comm, ← h1]; zify; repeat rw [Nat.cast_sub]
        push_cast; rw [Nat.cast_sub]; push_cast; ring; calc
          _ < 2 ^ 2 * 9 := by norm_num
          _ ≤ _ := by gcongr
        omega; calc
          _ ≤ p ^ 2 * 9 := by apply mul_le_mul; rw [pow_two]; apply Nat.le_mul_self; all_goals simp
          _ ≤ _ := by zify; rw [Nat.cast_sub]; ring_nf; simp; rw [← zero_add 1, Nat.add_one_le_iff]; positivity
        ring_nf; calc
          _ ≤ p ^ 2 * 9 := by apply mul_le_mul; rw [pow_two]; apply Nat.le_mul_self; all_goals simp
          _ ≤ _ := by
            zify; rw [Nat.cast_sub]; ring_nf; simp
            rw [← zero_add 1, Nat.add_one_le_iff]; positivity
        zify; rw [mul_le_mul_left (by simp), ← sub_nonneg, ← mul_le_mul_right (show 0<((2:ℤ)*(f p)+3*p+2*k) by positivity)]
        rw [hk, zero_mul]; positivity
        zify; rw [← sub_nonneg, ← mul_le_mul_right (show 0<((2:ℤ)*(f p)+3*p+2*k) by positivity)]
        rw [hk, zero_mul]; positivity
      -- In the second case, after simplifying all the assumptions, we will get $4 * f p = 3 * p ^ 2 - 6 * p + 3$
      · symm at hbc; simp at hu hij; simp only [hu, pow_zero, mul_one] at hbc h1; replace hbc : c = 3 := by omega
        rw [hbc, hij] at h2; right; right; left
        apply_fun fun t => t - 3 at h2; nth_rw 2 [← h1] at h2; rw [Nat.add_sub_sub_cancel, ← two_mul] at h2
        apply_fun fun t => 2 * t at h1; rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, h2] at h1
        rw [Nat.mul_add] at h1; symm at h1; rw [← Nat.sub_eq_iff_eq_add] at h1; ring_nf at h1
        rw [mul_comm, ← h1]; zify; repeat rw [Nat.cast_sub]
        push_cast; rw [Nat.cast_sub]; push_cast; ring; apply Nat.le_mul_of_pos_left; positivity
        rw [pow_two, ← mul_assoc, mul_le_mul_right]; any_goals omega
      -- In the third case, after simplifying all the assumptions, we will get $4 * f p = (p - 3) ^ 2$
      · symm at hbc; simp only [Nat.reducePow, zero_add] at hu hij; simp only [hu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_eq_left₀, pow_zero, mul_one] at hbc h1; rw [hbc, hij, one_mul] at h2
        right; left; by_cases hp : p ≤ 2
        · replace hp : p = 2 := by omega
          rw [hp, add_comm, ← add_assoc] at h2; omega
        apply_fun fun t => t - 9 at h2; nth_rw 1 [← h1, Nat.add_sub_sub_cancel, ← two_mul] at h2
        apply_fun fun t => 2 * t at h1; rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, h2] at h1
        rw [Nat.mul_add] at h1; symm at h1; rw [← Nat.sub_eq_iff_eq_add] at h1; ring_nf at h1
        rw [mul_comm, ← h1]; zify; repeat rw [Nat.cast_sub]
        push_cast; rw [Nat.cast_sub]; push_cast; ring
        rw [show 9 = 3^2 by simp, pow_le_pow_iff_left₀]; any_goals omega
      -- In the fourth case, after simplifying all the assumptions, we will get $f p = p$
      · symm at hbc; simp only [pow_zero] at hu hij; simp only [hu, one_mul, pow_one] at hbc h1; replace hij : j = 1 := by omega
        rw [hbc, hij, pow_one] at h2; left
        apply_fun fun t => t - p at h2; nth_rw 3 [← h1] at h2; rw [Nat.add_sub_sub_cancel, ← two_mul] at h2
        apply_fun fun t => 2 * t at h1; rw [Nat.mul_sub, Nat.sub_eq_iff_eq_add, h2] at h1
        rw [Nat.mul_add] at h1; symm at h1; rw [← Nat.sub_eq_iff_eq_add] at h1; ring_nf at h1
        simp only [← Nat.mul_sub_one, Nat.reduceSub, ← Nat.mul_add, Nat.reduceAdd, ← Nat.mul_sub,
          mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at h1; symm; exact h1
        simp only [← mul_assoc, Nat.reduceMul, ← Nat.sub_one_mul, Nat.add_one_sub_one, ←
          Nat.add_mul, Nat.reduceAdd]; rw [mul_le_mul_right]; any_goals omega
      -- The rest five cases are trivially ruled out by linarith
      · symm at hbc; simp at hu hij; rw [hu] at hbc h1; replace hij : j = 1 := by omega
        replace hbc : c = 3 := by omega
        rw [pow_one] at h1; rw [hbc, hij, pow_one, add_comm, ← add_assoc] at h2; simp only [add_left_eq_self,
          AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h2; omega
      · symm at hbc; simp only [Nat.reducePow] at hu hij; simp only [hu, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, pow_one] at hbc h1; replace hij : j = 1 := by omega
        rw [hij, hbc, pow_one, one_mul, add_comm, ← add_assoc] at h2
        suffices : p < 3 * p; omega; rw [Nat.lt_mul_iff_one_lt_left]; all_goals omega
      · symm at hbc; simp only [pow_zero, add_right_eq_self] at hu hij; simp only [hu,
        one_mul] at hbc h1; simp only [hbc, hij, pow_zero, mul_one] at h2
        rw [add_comm, ← add_assoc] at h2; have : p = 2 := by omega
        simp [this] at h2; suffices : Even 3; contradiction; rw [← h2]; use k+f 2; ring
      · symm at hbc; simp only [pow_one, add_right_eq_self] at hu hij; simp only [hu] at hbc h1; replace hbc : c = 3 := by omega
        simp only [hbc, hij, pow_zero, mul_one] at h2; rw [add_comm, ← add_assoc] at h2; omega
      · symm at hbc; simp at hu hij; simp only [hu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_eq_left₀] at hbc h1; simp [hbc, hij] at h2
        rw [add_comm, ← add_assoc] at h2; omega
      zify; rw [← sub_nonneg, ← mul_le_mul_right (show 0<((2:ℤ)*(f p)+3*p+2*k) by positivity)]
      rw [hk, zero_mul]; positivity
  -- From the explicity expressions given by the key lemma, it is not hard to see $f(p)$ can be arbitrarily large
    have fbig : ∀ N, ∃ p, p.Prime ∧ N < f p := by
      let k (p : ℕ) := 4 * p ⊓ ((p - 3) ^ 2) ⊓ (3 * p ^ 2 - 6 * p + 3) ⊓ (3 * p - 1) ^ 2
      -- Take advantage of the key lemma
      have hlb (p : ℕ) : p.Prime → k p ≤ 4 * f p := by
        intro hp
        have key' := key p hp
        obtain h | h | h | h := key'
        · rw [h]; dsimp [k]
          rw [min_assoc, min_assoc]
          exact inf_le_left
        · rw [h]; dsimp [k]
          rw [min_assoc, min_comm, ← min_assoc]
          exact inf_le_right
        · rw [h]; dsimp [k]
          rw [min_assoc]
          nth_rw 3 [min_comm]
          rw [← min_assoc]
          exact inf_le_right
        · rw [h]; dsimp [k]
          exact inf_le_right
      -- A rough lower bound, the only importance is that it increases a $p$ increases.
      have hlb' (p : ℕ) : 9 ≤ p → 4 * p ≤ k p := by
        intro hp
        simp only [k, Nat.min_assoc, le_inf_iff, le_refl, true_and]
        constructor
        -- $4 p ≤ (p - 3)^2$ if $9 ≤ p$
        · have h : 4 * (p : ℤ) ≤ ((p : ℤ) - 3) ^ 2  := by nlinarith
          zify; have : 3 ≤ p := by omega
          rw [(show ↑(p - 3) = (p : ℤ) - 3 by norm_cast)]
          exact h
        · constructor
          -- $4 p ≤ 3 p^2 - 6 p + 3$ if $3 ≤ p$
          · have h : 4 * (p : ℤ) ≤ 3 * (p : ℤ) ^ 2 - 6 * (p : ℤ) + 3 := by nlinarith
            zify
            have : 6 * p ≤ 3 * p ^ 2 := by nlinarith
            norm_cast at h
            norm_cast
          -- $4 p ≤ (3 p - 1)^2$ if $1 ≤ p$
          · have h : 4 * (p : ℤ) ≤ (3 * (p : ℤ) - 1) ^ 2 := by
              nlinarith
            have : 1 ≤ 3 * p := by omega
            zify;
            rw [show ↑(3 * p - 1) ^ 2 = (3 * (p : ℤ) - 1) ^ 2 by norm_cast]
            exact h
      -- Combine the above estimates
      intro N
      obtain ⟨p, hp⟩ := Nat.exists_infinite_primes (N + 9)
      use p
      constructor
      · exact hp.right
      · have : 4 * N < 4 * f p := calc
          _ < 4 * p := Nat.mul_lt_mul_of_pos_left (show N < p by omega) (show 4 > 0 by norm_num)
          _ ≤ k p := hlb' p (show 9 ≤ p by omega)
          _ ≤ 4 * f p := hlb p hp.right
        exact Nat.lt_of_mul_lt_mul_left this
  -- To prove the main goal, we assume the contrary that $f(x)≠x$ and discuss two cases when $x< f(x)$ or $f(x)< x$
    intro x xpos; by_contra!; rw [ne_iff_lt_or_gt] at this; rcases this with hx|hx
    -- In the first case, we specialize fbig at a number large enough to get a prime $p$ such that $f(p)$ is large
    -- then rearrange terms and use properties of integers to find a linear arithmetic contradiction
    · obtain ⟨p, ppr, fpgt⟩ := fbig ((x ^ 2 - x * f x + 1 - 2 * x) / 2 + 1)
      have := ppr.two_le; obtain ⟨t, ht⟩ := hsq x xpos p (show _ by omega); specialize fpos p ppr.pos
      zify at ht; rw [show (x:ℤ)*(f x)+(f p)^2+2*x*(f p) = (f p+x)^2-(x^2-x*f x) by ring, ← pow_two] at ht
      rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at ht; have : t < f p + x := by
        rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]; zify
        rw [← sub_pos, ht, sub_pos, pow_two]; norm_cast; rw [mul_lt_mul_left]; all_goals omega
      rw [Nat.lt_iff_add_one_le] at this; zify at this; rw [← le_sub_iff_add_le] at this
      rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), ← sub_le_sub_iff_left ((((f p):ℤ) + ↑x) ^ 2)] at this
      rw [ht, sq_sub_sq, sub_sub_self, mul_one] at this; ring_nf at this
      rw [← Nat.lt_sub_iff_add_lt, Nat.div_lt_iff_lt_mul, Nat.sub_one_mul] at fpgt
      by_cases h' : 2 * x ≤ x ^ 2 - x * f x + 1
      · rw [Nat.sub_lt_iff_lt_add] at fpgt; zify at fpgt
        rw [Nat.cast_sub, Nat.cast_sub] at fpgt; push_cast at fpgt; all_goals omega
      push_neg at h'; zify at h'; rw [Nat.cast_sub] at h'; push_cast at h'; omega
      rw [pow_two, mul_le_mul_left]; all_goals omega
  -- In the second case, we specialize fbig at another large number to get a prime $p$ such that $f(p)$ is large
  -- then rearrange terms and use properties of integers to find a linear arithmetic contradiction
    obtain ⟨p, ppr, fpgt⟩ := fbig ((x * f x - x ^ 2 - 1 - 2 * x) / 2 + 1)
    have := ppr.two_le; obtain ⟨t, ht⟩ := hsq x xpos p (show _ by omega); specialize fpos p ppr.pos
    zify at ht; rw [show (x:ℤ)*(f x)+(f p)^2+2*x*(f p) = (f p+x)^2+(x*f x - x^2) by ring, ← pow_two] at ht
    symm at ht; rw [← sub_eq_iff_eq_add'] at ht; have : f p + x < t := by
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]; zify
      rw [← sub_pos, ht, sub_pos, pow_two]; norm_cast; rw [mul_lt_mul_left]; all_goals omega
    rw [Nat.lt_iff_add_one_le] at this; zify at this
    rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), ← sub_le_sub_iff_right ((((f p):ℤ) + ↑x) ^ 2)] at this
    rw [ht, sq_sub_sq, add_sub_cancel_left, mul_one] at this; ring_nf at this
    rw [← Nat.lt_sub_iff_add_lt, Nat.div_lt_iff_lt_mul, Nat.sub_one_mul, Nat.sub_sub] at fpgt
    by_cases h' : 2 * x + 1 ≤ x * f x - x ^ 2
    · rw [Nat.sub_lt_iff_lt_add] at fpgt; zify at fpgt
      rw [Nat.cast_sub, Nat.cast_sub] at fpgt; push_cast at fpgt; ring_nf at fpgt
      rw [add_assoc] at fpgt; nth_rw 2 [add_comm] at fpgt; all_goals omega
    push_neg at h'; zify at h'; rw [Nat.cast_sub] at h'; push_cast at h'; omega
    rw [pow_two, mul_le_mul_left]; all_goals omega
-- Conversely, if $f(x)=x$ then it is straightforward to check the expression in question is a square
  intro h x xpos y ypos; have fx := h x xpos; have fy := h y ypos
  use x+y; rw [fx, fy]; ring
