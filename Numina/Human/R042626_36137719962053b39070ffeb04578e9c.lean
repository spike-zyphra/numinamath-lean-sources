import Mathlib

/- Problem 4. Consider a non-zero natural number $n$ and the function


$$

f: \mathbb{N} \rightarrow \mathbb{N}, f(x)=\left\{\begin{array}{c}
\frac{x}{2} \quad, \text { if } x \text { is even } \\
\frac{x-1}{2}+2^{n-1}, \text { if } x \text { is odd }
\end{array}\right.

$$


Determine the set


$$

A=\{x \in \mathbb{N} \mid(\underbrace{f \circ f \circ \ldots \circ f}_{\text {of } n \text { times } f})(x)=x\}

$$
 -/

theorem number_theory_117563 {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℕ)
    (hf : ∀ x, Even x → f x = x / 2)
    (hf' : ∀ x, Odd x → f x = (x - 1) / 2 + 2 ^ (n - 1)) :
    {x | f^[n] x = x} = {x | x ∈ Finset.range (2 ^ n) } := by  {
  apply Set.ext
  intro x
  simp
  -- function f is decreasing when x ≥ 2^n
  have hl: ∀ x, 2^n ≤ x → f x < x := by {
    intro x h
    have h0: 0 < x := by {
      apply lt_of_lt_of_le _ h
      simp
    }
    by_cases h2: Even x; {
      apply hf at h2
      rw[h2]
      apply Nat.div_lt_self h0
      simp
    }; {
      simp at h2
      have ht2: (x - 1) + 2 ^ (n - 1)*2 < x*2 := by {
        rw[add_comm]
        apply Nat.add_lt_of_lt_sub
        rw[tsub_tsub_assoc]; {
          rw[<-mul_one x, mul_assoc, <-Nat.mul_sub, Nat.lt_add_one_iff]
          simp
          convert h using 1
          exact pow_sub_one_mul hn 2
        }
        apply Nat.le_mul_of_pos_right; simp
        apply Nat.succ_le_of_lt h0
      }
      have ho: Odd x := h2
      apply hf' at h2
      rw[h2]
      apply Nat.lt_of_mul_lt_mul_right
      rw [Nat.add_mul]
      convert ht2 using 2
      apply Nat.div_mul_cancel
      cases ho with | intro k hk =>
      use k
      rw[hk]
      simp
    }
  }
  -- function f maps range from 0 to 2^n-1 to itself
  have hq: ∀ x, x < 2^n-1 → f x < 2^n-1 := by {
    intro x hx
    by_cases h2: Even x; {
      apply hf at h2
      rw[h2]
      apply lt_of_le_of_lt _ hx
      apply Nat.div_le_self
    }; {
      simp at h2
      have ho: Odd x := h2
      apply hf' at h2
      rw[h2]
      apply Nat.add_lt_of_lt_sub
      rw[<-Nat.sub_one_add_one hn, pow_add, pow_one, Nat.sub_one_add_one, <-mul_one (2 ^ (n - 1))];{
        rw[mul_assoc, Nat.sub_sub, Nat.add_comm, <-Nat.sub_sub, <-Nat.mul_sub]
        simp
        cases ho with | intro k hk =>
        rw[hk, Nat.add_one_sub_one, mul_comm, Nat.mul_div_cancel]
        have h02: 0 < 2 := by exact Nat.ofNat_pos
        rw[<-Nat.mul_lt_mul_right h02, Nat.sub_mul, <-Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_one_add_one hn]
        rw[hk, Nat.lt_sub_iff_add_lt] at hx
        rw[Nat.lt_sub_iff_add_lt]
        simp
        rw[mul_comm]
        convert hx
        simp
      }
      exact hn
    }
  }
  -- function f maps the number 2^n - 1 into itself
  have ht: f (2^n - 1) = 2^n-1 := by {
    rw[hf', Nat.sub_sub]
    simp
    have h2: (2 ^ n - 2) = (2^(n-1) - 1) *2 := by {
      rw[Nat.sub_mul, <-Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_one_add_one]
      exact hn
    }
    rw [h2, Nat.mul_div_cancel, <-Nat.sub_add_comm, <-Nat.mul_two, <-Nat.pow_succ]
    rw[Nat.succ_eq_add_one, Nat.sub_one_add_one]
    exact hn
    apply Nat.one_le_pow
    simp
    simp
    use (2^(n-1) -1)
    norm_num
    rw[Nat.mul_sub, mul_comm, <-Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_one_add_one]
    simp
    rw[Nat.sub_add_cancel]
    apply Nat.le_self_pow hn
    exact hn
  }
  -- function f maps range from 0 to 2^n to itself
  have hr: ∀ x, x < 2^n → f x < 2^n := by {
    intro x hx
    by_cases he: x = 2^n - 1; {
      rw[he, ht]
      simp
    }; {
      apply lt_trans
      apply hq
      apply Nat.lt_of_le_of_ne _ he
      apply Nat.le_sub_one_of_lt hx
      simp
    }
  }
  -- If x is at lest 2^n, then all iterations of f are smaller than x. So x must be smaller than 2^n
  have hi: ∀ k x: ℕ, 2^n ≤ x -> f^[k+1] x < x := by {
    intro k
    induction k with
    | zero => {
      intro x hx
      simp
      apply hl
      apply hx
    }
    | succ k hk => {
      intro x hx
      rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
      by_cases ht: 2^n ≤ f^[k + 1] x; {
        apply lt_trans
        apply hl
        exact ht
        apply hk
        apply hx
      }; {
        rw[not_le] at ht
        apply lt_of_lt_of_le _ hx
        apply hr
        exact ht
      }
    }
  }
  -- x equals 2 f(x) mod 2^n - 1, so x equals 2^k f^[k](x) mod 2^n - 1
  have hd: ∀ k x, x < 2^n -> 2^k * f^[k] x % (2^n - 1)= x % (2^n - 1) := by {
    intro k
    induction k with
    | zero => simp
    | succ k hk => {
      simp
      intro x hx
      rw[Nat.pow_succ, mul_comm (2^k), mul_assoc, mul_comm, Nat.mul_two, Nat.add_mod, hk, <- Nat.add_mod]
      rw[<-mul_two]
      by_cases h2: Even x; {
        have he: Even x := h2
        apply hf at h2
        rw[h2, Nat.div_mul_cancel]
        exact even_iff_two_dvd.mp he
      }; {
        simp at h2
        have ho: Odd x := h2
        apply hf' at h2
        rw[h2, add_mul, Nat.div_mul_cancel, <-Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_one_add_one hn]
        rw[<-Nat.sub_add_comm, Nat.add_sub_assoc, Nat.add_mod]
        simp; {
          apply Nat.one_le_pow; simp
        }; {
          cases ho with |intro t ht =>
          rw[ht]
          simp
        }
        cases ho with |intro t ht =>
        use t
        rw [ht]
        simp
      }
      apply hr
      exact hx
    }
  }
  apply Iff.intro; {
    cases n with
    | zero => tauto
    | succ k =>
      intro h
      by_contra h2
      simp at h2
      apply hi at h2
      rw [h] at h2
      rw[lt_self_iff_false] at h2
      exact h2
  }; {
    intro h
    -- if x < 2^n - 1, we use the fact that x equals 2^n f^[n](x) mod 2^m - 1 to deduce they are equal
    by_cases he: x < 2^n - 1; {
      have hm: (2^n - 1 + 1)* f^[n] x % (2 ^ n - 1) = x % (2 ^ n - 1) := by {
        rw[Nat.sub_one_add_one]
        apply hd
        exact h
        simp
      }
      rw[Nat.add_mul, Nat.add_mod] at hm
      simp at hm
      rw[Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at hm
      exact hm
      exact he
      have hak: ∀ k x, x < 2^n - 1 -> f^[k] x < 2 ^ n - 1 := by {
        intro k
        induction k with
        |zero => simp;
        |succ k hk => {
          intro x hx
          simp
          apply hk
          apply hq
          apply hx
        }
      }
      apply hak
      exact he
    };{
      -- if x = 2^n - 1, it is a stationary point.
      rw[not_lt] at he
      have hx: x = 2^n - 1 := by {
        apply Nat.eq_of_le_of_lt_succ he
        rw[Nat.sub_one_add_one]
        exact h
        simp
      }
      rw[hx]
      have hk: ∀ k, f^[k] (2 ^ n - 1) = 2 ^ n - 1 := by {
        intro k
        induction k with
        |zero => simp
        |succ k hk => {
          simp
          rw[ht, hk]
        }
      }
      apply hk
    }
  }
}