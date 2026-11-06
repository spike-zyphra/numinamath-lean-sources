import Mathlib

open Finset

/- Find a function $f(m, n)$ that satisfies the following conditions for every pair of non-negative integers $m, n$:
1. \( 2f(m, n) = 2 + f(m+1, n-1) + f(m-1, n+1) \) for \( m \geq 1 \) and \( n \geq 1 \);
2. \( f(m, 0) = f(0, n) = 0 \).
(1993 Korean Olympiad Problem)-/
theorem recursion_4201 {f : ℕ → ℕ → ℤ} (hm : ∀ m, f m  0 = 0) (hn : ∀ n, f 0 n = 0)
    (hmn : ∀ m n, 2*f (m+1) (n+1) = 2+f (m+2) n + f m (n+2)) :
    ∀ m n, f m n = m * n := by
  -- rewrite 2f(m+1,n+1) = 2 + f(m+2,n) + f(m,n+2) to
  -- f(m+1,n+1) - f(m,n+2) = f(m+2,n) - f(m+1,n+1) + 2
  have H m n : f (m+1) (n+1) - f m (n+2) = f (m+2) n - f (m+1) (n+1) + 2 := by
    linear_combination hmn m n
  -- assign m=m-k, n=n+k to H
  -- sum from k=0 to k=m
  -- we have f(m+1,n+1) = f(m+2,n) - f(1,n+m+1) + 2(m+1)
  have H1 m n : f (m+1) (n+1) = f (m+2) n - f 1 (n+m+1) + 2*(m+1) := by
    let F : ℕ → ℤ := fun i => f (m+1-i) (n+1+i)
    let G : ℕ → ℤ := fun i => f (m-i+2) (n+i) - f (m-i+1) (n+i+1) + 2
    have := sum_range_sub' F (m+1)
    have hFG : ∀ i ∈ range (m+1), F i - F (i+1) = G i := by
      intro i hi
      simp [F, G]
      have : m+1-i=m-i+1 := by
        refine Nat.sub_add_comm ?h
        simp at hi
        linarith
      rw [← H (m-i) (n+i), this]
      ring_nf
    rw [sum_congr rfl hFG] at this
    simp [F, hn] at this
    rw [← this]
    simp [G]
    rw [sum_add_distrib, sum_const, mul_comm 2]
    simp
    have := sum_range_sub' (fun i => f (m+2-i) (n+i)) (m+1)
    simp at this
    rw [← add_assoc] at this
    rw [← this]
    have h1 : ∑ x ∈ range (m + 1), f (m - x + 2) (n + x) =
        ∑ x ∈ range (m + 1), f (m + 2 - x) (n + x) := by
      refine sum_congr rfl (fun x hx => ?_)
      rw [← Nat.sub_add_comm]
      simp at hx
      linarith
    have h2 : ∑ x ∈ range (m + 1), f (m - x + 1) (n + x + 1) =
        ∑ x ∈ range (m + 1), f (m + 1 - x) (n + (x + 1)) := by
      refine sum_congr rfl (fun x hx => ?_)
      rw [← add_assoc, ← Nat.sub_add_comm]
      simp at hx
      linarith
    linear_combination h1 - h2
  -- assign m=m+k, n=n-k to H1
  -- sum from k=0 to k=n
  -- we have f(m+1,n+1) = -(n+1)f(1,n+m+1) + 2(m+1)(n+1) + n(n+1)
  have H2 m n : f (m+1) (n+1) = -(n+1)*f 1 (n+m+1) + 2*(m+1)*(n+1) + n*(n+1) := by
    have := sum_range_sub' (fun i => f (m+1+i) (n+1-i)) (n+1)
    conv at this => rhs; simp [hm]
    rw [← this]
    calc
      _ = ∑ x ∈ range (n+1), (-f 1 (m+n+1)+2*(m+x+1)) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [show m+1+x=m+x+1 by ring]
        rw [show n+1-x=n-x+1 by rw [← Nat.sub_add_comm]; simp at hx; linarith]
        rw [H1 (m+x) (n-x)]
        rw [show m+1+(x+1)=m+x+2 by ring]
        rw [show n+1-(x+1)=n-x from Nat.add_sub_add_right n 1 x]
        rw [show n-x+(m+x)+1=m+n+1 by
          rw [add_right_cancel_iff, add_comm (n-x), add_assoc, add_left_cancel_iff, add_comm]
          exact Nat.sub_add_cancel (by simp at hx; linarith)]
        norm_cast
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_const]
        rw [← mul_sum, sum_add_distrib, sum_const]
        rw [mul_add, sum_add_distrib, sum_const]
        have : 2 * ∑ x ∈ range (n+1), (x : ℤ) = n*(n+1) := calc
          _ = (2 : ℤ) * ∑ x ∈ range (n+1), x := by push_cast; rfl
          _ = _ := by
            norm_cast
            rw [mul_comm 2, sum_range_id_mul_two]
            simp [mul_comm]
        rw [mul_add, this]
        simp
        ring_nf
  -- by showing that f(1,m)=m, we have f(1,n+m+1)=f(n+m+1,1)
  have f_one_m m : f 1 m = m := by
    rcases m with _ | m
    rw_mod_cast [hm]
    have := H2 0 m
    simp at this
    rw [← mul_right_inj' <| show (m : ℤ) + 2 ≠ 0 from Ne.symm (OfNat.zero_ne_ofNat (m + 2))]
    rw [add_assoc, ← add_mul] at this
    push_cast
    linear_combination this
  -- combining above results, we can deduce that f(n,m) is multiplication for positive integers
  intro m n
  rcases m with _ | m
  . simp [hn]
  rcases n with _ | n
  . simp [hm]
  rw [H2 m n, f_one_m]
  push_cast
  ring
