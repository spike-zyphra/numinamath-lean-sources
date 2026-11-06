import Mathlib

/- A natural number $n$ is said to be perfect if the sum of all its proper divisors, that is, divisors different from $n$, is equal to $n$. For example, 6 and 28 are perfect, since $6=1+2+3$ and $28=1+2+4+7+14$. Knowing that $2^{31}-1$ is a prime number, show that $2^{30}\left(2^{31}-1\right)$ is a perfect number. -/

theorem number_theory_257462 {n : ℕ} (hn : n = 2^30 * (2^31 - 1))
(hp: Nat.Prime (2^31 - 1)) :
∑ d in n.properDivisors, d = n := by {
  -- Proper divisors of n are either powers of 2 or powers of 2 multiplied by (2^31 - 1)
  have hd: n.properDivisors = Finset.image ( fun x=> 2^x) (Finset.Ico 0 31) ∪ Finset.image ( fun x=> 2^x*(2^31-1)) (Finset.Ico 0 30):= by {
    apply Finset.ext
    intro a
    rw[Nat.properDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    apply Iff.intro; {
      intro ha
      cases ha with | intro han ha =>
      rw[hn, Nat.dvd_mul] at ha
      cases ha with | intro s ha =>
      cases ha with | intro t ha =>
      cases ha with | intro hs ha =>
      cases ha with | intro ht hst =>
      rw[Nat.dvd_prime] at ht
      cases ht with
      | inl ht => {
        left
        rw[Nat.dvd_prime_pow] at hs; {
          cases hs with | intro k hs =>
          cases hs with | intro hk hs =>
          use k
          apply And.intro; {
            rw[Finset.mem_Ico]
            apply And.intro; simp
            exact Nat.lt_add_one_of_le hk
          }; {
            rw [←hs, ←hst, ht, mul_one]
          }
        }
        norm_num
      }
      |inr ht => {
        right
        rw[Nat.dvd_prime_pow] at hs; {
          cases hs with | intro k hs =>
          cases hs with | intro hk hs =>
          use k
          apply And.intro; {
            rw[Finset.mem_Ico]
            apply And.intro; simp
            apply lt_of_le_of_ne hk
            intro h30
            cases han with | intro h1 han =>
            rw [hn, ←hst, hs, ht, h30, lt_self_iff_false] at han
            exact han
          }; {
            rw [←hs, ←hst, ht]
          }
        }
        norm_num
      }; {
        exact hp
      }
    }; {
      intro ha
      apply And.intro; {
        apply And.intro; {
          rw [Nat.add_one_le_iff, ←Nat.ne_zero_iff_zero_lt]
          intro h0; revert ha
          rw [h0]
          simp
        }; {
          cases ha with
          |inl ha => {
            cases ha with | intro b ha =>
            cases ha with | intro hb ha =>
            simp at hb
            rw [←ha, hn, ←mul_one (2^b)]
            apply Nat.mul_lt_mul_of_le_of_lt; {
              rw[Nat.pow_le_pow_iff_right]
              apply Nat.le_of_lt_add_one
              exact hb
              simp
            }; simp; simp
          }
          |inr ha => {
            cases ha with | intro b ha =>
            cases ha with | intro hb ha =>
            simp at hb
            rw [←ha, hn, Nat.mul_lt_mul_right, Nat.pow_lt_pow_iff_right]
            exact hb
            simp
            simp
          }
        }
      }; {
        cases ha with
        |inl ha => {
          cases ha with | intro b ha =>
          cases ha with | intro hb ha =>
          simp at hb
          rw [←ha, hn]
          use 2^(30-b)*(2^31-1)
          rw [←mul_assoc, Nat.mul_left_inj, ←Nat.pow_add, add_comm, Nat.sub_add_cancel]
          apply Nat.le_of_lt_add_one hb
          simp
        }
        |inr ha => {
          cases ha with | intro b ha =>
          cases ha with | intro hb ha =>
          simp at hb
          rw [←ha, hn]
          use 2^(30-b)
          rw [mul_comm (2 ^ b * (2 ^ 31 - 1)), ←mul_assoc, ←Nat.pow_add, Nat.sub_add_cancel]
          exact Nat.le_of_succ_le hb

        }
      }
    }
  }
  -- So, sum over divisors can be rewritten as a sum of two geometric progresions
  rw[hd, Finset.sum_union, Finset.sum_image, Finset.sum_image]

  -- Sum in each progression can be computed using the geometric progression summation formula
  have h2: ∀ k, ∑ x ∈ Finset.Ico 0 k, 2 ^ x = 2^k - 1 := by {
    intro k
    induction k with
    |zero => simp
    |succ k hk => {
      rw [Finset.sum_Ico_succ_top, hk, pow_add, pow_one, mul_two, ←Nat.sub_add_comm]
      apply Nat.one_le_pow
      simp
      simp
    }
  }
  have h2p: ∀ k b, ∑ x ∈ Finset.Ico 0 k, (2 ^ x)*b = (2^k - 1)*b := by {
    intro k b
    rw[←Finset.sum_mul, h2]
  }
  rw[h2, h2p, hn, ← one_mul (2^31-1), ←mul_assoc, ←add_mul, one_mul, mul_one, add_comm, Nat.sub_add_cancel]
  simp
  {
    intro x hx y hy h
    rw [Nat.mul_left_inj] at h
    apply Nat.pow_right_injective at h
    exact h
    simp
    simp
  }; {
    intro x hx y hy h
    apply Nat.pow_right_injective at h
    exact h
    simp
  };
  -- It is important to note that those geometric progressions are disjoint.
  {
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h
    simp at hx
    simp only [Finset.mem_image, Finset.mem_Ico, Nat.zero_le, true_and] at hy
    cases hx with | intro a hx =>
    cases hx with | intro ha hx =>
    cases hy with | intro b hy =>
    cases hy with | intro hb hy =>
    rw [h, ←hy] at hx
    apply congrArg (fun x => x % (2^31 - 1))at hx
    rw[Nat.mul_mod_left, ←Nat.dvd_iff_mod_eq_zero] at hx
    apply Nat.prime_eq_prime_of_dvd_pow at hx
    simp at hx
    exact hp
    norm_num
  }
}