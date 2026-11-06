import Mathlib

/- Find all positive integers $k$ such that the product of the digits of $k$, in the decimal system, equals

$$
\frac{25}{8} k-211
$$ -/
theorem number_theory_607988 (k : ℕ) :
    (Nat.digits 10 k).prod = (25 / 8 : ℝ) * k - 211 ↔ k = 72 ∨ k = 88 :=
by
  constructor; swap
  . -- The first case is very easy
    rintro (h|h)
    . subst h
      simp; linarith
    . subst h
      simp; linarith
  . intro h
    -- Let
    -- $$ a=\\sum\_{k=0}^{n} a\_{k} 10^{k}, \\quad 0 \\leq a\_{k} \\leq 9, \\text { for } 0 \\leq k \\leq n-1,1 \\leq a\_{n} \\leq 9 $$

    let a := Nat.digits 10 k
    have adef : a = Nat.digits 10 k := by rfl
    -- Set
    -- $$ f(a)=\\prod\_{k=0}^{n} a\_{k} $$

    -- Since
    -- $$ f(a)=\\frac{25}{8} a-211 \\geq 0 $$
    -- $a \\geq \\frac{8}{25} \\cdot 211=\\frac{1688}{25}&gt;66$.
    have k_gt_66 : k > 66 := by
      qify
      calc
        k ≥ (8 : ℚ)/25 * 211 := by
          have : 25/8*(k : ℚ)-211 ≥ 0 := by
            rify
            rewrite [←h]
            exact Nat.cast_nonneg' (Nat.digits 10 k).prod
          linarith
        _ = 1688/25 := by ring_nf
        _ > 66 := by
          have : (1688 : ℚ)/25 = 67 + 13/25 := by ring_nf
          rewrite [this]
          linarith
    -- Also, $f(a)$ is an integer, so, we have $\frac{8}{25} a$ is an integer.
    have : 8 ∣ 25 * k := by
      simp [Dvd.dvd]
      use a.prod + 211
      have : 25 / 8 * (k : ℝ)  = a.prod + 211 := by
        simp only [a]
        linarith
      have : 25 * (k : ℝ)  = 8 * (a.prod + 211) := by linarith
      let x := a.prod
      have xdef : x = a.prod := by rfl
      rewrite [←xdef] at this
      rewrite [←xdef]
      rify
      assumption
    -- and $\\operatorname{gcf}(8,25)=1$, so $8 \\mid a$.
    have k_dvd: 8 ∣ k := by
      zify
      zify at this
      apply Int.dvd_of_dvd_mul_right_of_gcd_one
      . exact this
      . rfl
    -- On the other hand,
    -- $$ f(a) \\leq 9^{n-1} a\_{n} \\leq 10^{n} a\_{n} \\leq a $$
    -- So
    have : (25 : ℚ)/8*k - 211 ≤ k := by
      let n := a.length
      have nonempty_a : a ≠ [] := by
        have : a.length > 0 := by
          by_contra x
          have : a.length = 0 := by linarith
          have : k = 0 := by
            simp[a] at this
            apply Nat.digits_eq_nil_iff_eq_zero.mp
            exact this
          linarith
        exact List.ne_nil_of_length_pos this
      have nonempty_rev_a : a.reverse ≠ [] := List.reverse_ne_nil_iff.mpr nonempty_a
      let last : ℕ := a.reverse.head nonempty_rev_a
      -- We will prove by chaining inequalities.
      calc
        (25 : ℚ)/8*k - 211 ≤ 9^(n-1)*last := by
          rify
          rewrite [←h]
          simp only [last, a]
          have rev_prod : ∀ (ls : List ℕ), ls.prod = ls.reverse.prod := by
            intro ls
            symm
            apply List.prod_reverse
          have : ∀ (ls : List ℕ) (ne : ls ≠ []), ls.prod = ls.head ne * ls.tail.prod := by
            intros ls ne
            have : ls.prod = (ls.head ne :: ls.tail).prod := by simp
            rewrite [this]
            simp only [List.prod, List.foldr]
          rewrite [rev_prod, this _ nonempty_rev_a]
          rewrite [mul_comm]
          -- This is use to rewrite the goal
          have r1 : ∀ (a a' b c : ℝ), a = a' → a ≥ 0 → b ≤ c → b * a ≤ c * a' := by
            intros _ _ _ _ eq _ _
            rewrite [eq] at *
            apply mul_le_mul_of_nonneg_right
            . assumption
            . assumption
          rify at this
          have r2 : @Nat.cast ℝ Real.instNatCast (a.reverse.tail.prod * a.reverse.head nonempty_rev_a) = @Nat.cast ℝ Real.instNatCast a.reverse.tail.prod * @Nat.cast ℝ Real.instNatCast (a.reverse.head nonempty_rev_a) := by simp
          rewrite [r2]
          simp only [a]
          apply r1; rfl
          . apply Nat.cast_nonneg'
          . -- We have $\\prod\_{k=0}^{n-1} a\_{k} \\leq 9^{n-1}$.
            have : ∀ x ∈ a.reverse, x ≤ 9 := by
              intro x h
              have : (x ≤ 9) = (x < 10) := by ext; constructor <;> intro x <;> linarith
              rewrite [this]
              apply Nat.digits_lt_base
              . simp
              . exact List.mem_reverse.mp h
            -- We have $\\prod\_{k=0}^{n-1} a\_{k} \\leq 9^{n-1}$.
            have H : ∀ x ∈ a.reverse.tail, x ≤ 9 := by
              intro x h
              apply this
              apply List.mem_of_mem_tail
              assumption
            -- We have $\\prod\_{k=0}^{n-1} a\_{k} \\leq 9^{n-1}$.
            have : (Nat.digits 10 k).reverse.tail.prod ≤ 9 ^ (n - 1) := by
              have : n - 1 = (Nat.digits 10 k).reverse.tail.length := by
                simp only [n]
                rewrite [←adef]
                have : a.length = a.reverse.length := by simp
                rewrite [this]
                symm
                apply List.length_tail
              rewrite [this]
              apply List.prod_le_pow_card
              simp only [a] at H
              assumption
            let u := (Nat.digits 10 k).reverse.tail.prod
            have udef: (Nat.digits 10 k).reverse.tail.prod = u := by rfl
            rewrite [udef]
            rewrite [udef] at this
            rify at this
            exact this
        _ ≤ 10^(n-1) * last := by
          have : 9 ^ (n - 1) ≤ 10 ^ (n - 1) := by
            apply Nat.pow_le_pow_left; simp
          have : 9 ^ (n - 1) * last ≤ 10 ^ (n - 1) * last := by
            apply Nat.mul_le_mul_right
            assumption
          qify at this
          apply this
        _ ≤ k := by
          have : 10 ^ (n - 1) * last ≤ k := by
            zify
            have H : ∀ (ls : List ℕ) (hls : ∀ x ∈ ls, x < 10) (x : ℕ) (hx : x < 10),
              x * 10^ls.length ≤ Nat.ofDigits (α := ℕ) 10 (ls ++ [x]) := by
                intro ls hls
                induction ls with
                | nil => simp;
                | cons x' xs ih =>
                    intros x xh
                    simp [Nat.ofDigits]
                    have : x * 10 ^ (xs.length + 1) = x * 10 * 10^xs.length := by ring_nf
                    rewrite [this]
                    have : x * 10 ^ xs.length * 10 ≤ x' + Nat.ofDigits (α := ℕ) 10 (xs ++ [x]) * 10 := by
                      have : x * 10 ^ xs.length ≤ Nat.ofDigits 10 (xs ++ [x]) := by
                        apply ih
                        . intro X XH
                          apply hls
                          simp; right; assumption
                        . assumption
                      calc
                        _ ≤ Nat.ofDigits (α := ℕ) 10 (xs ++ [x]) * 10 := Nat.mul_le_mul_right 10 this
                        _ ≤ _ := by linarith
                    ring_nf at this
                    ring_nf
                    exact this
            simp only [n, last, a]
            have : 10 ^ ((Nat.digits 10 k).length - 1) * (Nat.digits 10 k).reverse.head nonempty_rev_a ≤ k := by
              let x := (Nat.digits 10 k).reverse.head nonempty_rev_a
              let ls := (Nat.digits 10 k).reverse.tail.reverse
              rewrite [mul_comm]

              have r : k = Nat.ofDigits 10 a := by
                symm
                apply Nat.ofDigits_digits
              have r : ∀ x, x ≤ Nat.ofDigits 10 a → x ≤ k := by rewrite [←r]; simp
              apply r
              have : a = ls ++ [x] := by
                simp[a, ls, x]
                symm
                apply List.dropLast_concat_getLast
              rewrite [this]
              have : (Nat.digits 10 k).length - 1 = ls.length := by simp[ls]
              rewrite [this]
              apply H ls
              . simp [ls]
                intro x xh
                apply Nat.digits_lt_base (m := k)
                simp
                apply List.mem_of_mem_dropLast
                assumption
              . apply Nat.digits_lt_base (m := k)
                simp
                apply List.mem_reverse.mp
                apply List.head_mem
            zify at this
            exact this
          qify at this
          exact this
    -- Thus we have $a \\leq \\frac{8}{17} \\cdot 211=\\frac{1688}{17}&lt;100$.
    have : k < 100 := by
      qify
      have : (25 : ℚ) / 8 * k - k - 211 ≤ 0 := by linarith
      have : (25 - 8: ℚ) / 8 * k - 211 ≤ 0 := by linarith
      have : (17 : ℚ) / 8 * k ≤ 211 := by linarith
      have : k ≤ (1688 : ℚ)/17 := by linarith
      have : 1688 / 18 < 100 := by ring_nf; simp
      linarith
    -- Now we can shrink the range.
    have : k ∈ ({72, 80, 88, 96} : Set ℕ) := by
      have r : k ∈ {x : ℕ | 66 < x ∧ x < 100 ∧ 8 ∣ x} := by simp; tauto
      have : {x : ℕ | 66 < x ∧ x < 100 ∧ 8 ∣ x} = {72, 80, 88, 96} := by
        ext x
        simp
        constructor <;> intro h
        . -- Enumerate every number in range
          have H : x ∈ List.range' 67 33 := by simp; tauto
          simp [List.range'] at H
          rcases h with ⟨_,_, h⟩
          -- Use `repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))` to simplify the proof.
          repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))
          tauto
          repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))
          tauto
          repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))
          tauto
          repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))
          tauto
          repeat (rcases H with (H1 | H); try (subst H1 ; norm_num at h))
          tauto
        . rcases h with (h|h|h|h) <;> subst h <;> norm_num
      rewrite [this] at r
      assumption
    simp at this
    (rcases this with (H|H|H|H) <;> try tauto)
    <;> exfalso
    <;> subst H
    <;> simp at h
    <;> ring_nf at h
    <;> norm_num at h
