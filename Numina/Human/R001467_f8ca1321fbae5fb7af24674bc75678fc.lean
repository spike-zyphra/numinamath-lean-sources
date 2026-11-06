import Mathlib

open Finset

/- 16. (ISR 1) The set $\left\{a_{0}, a_{1}, \ldots, a_{n}\right\}$ of real numbers satisfies the following conditions: (i) $a_{0}=a_{n}=0$; (ii) for $1 \leq k \leq n-1$,  $$ a_{k}=c+\sum_{i=k}^{n-1} a_{i-k}\left(a_{i}+a_{i+1}\right) . $$  Prove that $c \leq \frac{1}{4 n}$. -/
-- change the assumption (ii) to be the index start with 0 $$ a_{k}=c+\sum_{i=k}^{n} a_{i-k}\left(a_{i}+a_{i+1}\right). $$
theorem algebra_24204 {n : ℕ} {c : ℝ} (hn : n ≥ 2) (a : ℕ → ℝ) (ha0 : a 0 = 0) 
    (han : a n = 0)
    (h : ∀ k ∈ Finset.Icc 0 (n - 1), a k = c + ∑ i ∈ Finset.Icc k (n - 1), a (i - k) * (a i + a (i + 1))) :
    c ≤ 1 / (4 * n) := by 
  let S : ℕ → ℝ := fun k => ∑ i ∈ Icc 0 k, a i
  -- S (n - 1) = S n
  have eq1 : S (n - 1) = S n := by 
    unfold S
    have seteq : Icc 0 n = insert n (Icc 0 (n - 1)) := by 
      have aux : n = (n - 1) + 1 := by 
        omega
      nth_rw 1 [aux]
      nth_rw 2 [aux]
      refine Eq.symm (Nat.Icc_insert_succ_right ?_)
      linarith
    rw [seteq, sum_insert]
    rw [han]
    simp
    simp
    linarith
  have hs0 : S 0 = 0 := by 
    unfold S
    simp
    exact ha0
  -- use the same method in the solution to prove the following property
  have eq2 : S n = n * c + (S n) ^ 2 := by 
    calc 
      _ = S (n - 1) := by 
        exact Eq.symm eq1
      _ = n * c + ∑ k ∈ Icc 0 (n - 1), (∑ i ∈ Icc k (n - 1), a (i - k) * (a i + a (i + 1))) := by 
        unfold S
        rw [sum_congr _ h, sum_add_distrib]
        have aux1 : ∑ x ∈ Icc 0 (n - 1), c  = n * c := by 
          simp
          left
          norm_cast
          omega
        rw [aux1]
        simp
      _ = n * c + ∑ i ∈ Icc 0 (n - 1), (∑ k ∈ Icc 0 i, a (i - k) * (a i + a (i + 1))) := by 
        simp
        -- change the sum order
        apply Finset.sum_comm'
        intro x y
        constructor
        · -- forward direction
          intro ⟨hx, hy⟩
          simp at hx hy
          simp
          constructor
          exact hy.1
          exact hy.2
        · -- backward direction
          intro ⟨hx, hy⟩
          simp
          simp at hx hy
          exact ⟨by linarith, hx, hy⟩
      _ = n * c + ∑ i ∈ Icc 0 (n - 1), ((a i + a (i + 1)) * ∑ k ∈ Icc 0 i, a (i - k)):= by 
        simp
        apply sum_congr rfl
        intro x hx 
        rw [mul_comm, sum_mul]
      _ = n * c + (S 1 * S 0 + ∑ i ∈ Icc 1 (n - 1), ((S (i + 1) - S (i - 1)) * S i))  := by 
        simp
        have aux : Icc 0 (n - 1) = insert 0 (Icc 1 (n - 1)) := by
          refine (erase_eq_iff_eq_insert ?_ ?_).mp rfl
          simp
          simp
        rw [aux, sum_insert]
        unfold S
        simp
        have aux2 : (∑ i ∈ Icc 0 1, a i) = a 0 + a 1 := by 
          refine sum_eq_add_of_mem 0 1 ?_ ?_ ?_ ?_
          simp
          simp
          norm_num
          intro c hc hc1
          by_contra hc2
          simp at hc
          omega
        
        rw [aux2]
        simp
        apply sum_congr rfl
        intro x hx
        have aux3 : (∑ i ∈ Icc 0 (x + 1), a i - ∑ i ∈ Icc 0 (x - 1), a i) = a x + a (x + 1) := by
          have aux5 : Icc 0 (x + 1) = insert (x + 1) (Icc 0 x) := by
            refine Eq.symm (Nat.Icc_insert_succ_right ?_)
            linarith
          have aux6 : Icc 0 x = insert x (Icc 0 (x - 1)) := by
            refine (erase_eq_iff_eq_insert ?_ ?_).mp ?_
            simp
            simp
            simp at hx
            linarith 
            simp
            refine Nat.range_eq_Icc_zero_sub_one x ?_
            simp at hx
            linarith
          rw [aux5, sum_insert, aux6, sum_insert]
          ring_nf
          simp at hx
          simp
          linarith
          simp
        have aux4 : ∑ k ∈ Icc 0 x, a (x - k) = ∑ k ∈ Icc 0 x, a k := by 
          let t : ℕ → ℕ := fun i => x - i
          refine sum_nbij' t t ?_ ?_ ?_ ?_ ?_
          simp
          · intro m ha 
            unfold t
            omega
          · intro m ha 
            unfold t
            simp at ha
            simp
          · intro m ha 
            unfold t
            simp at ha
            omega
          · intro m ha
            unfold t 
            simp at ha
            omega
          · intro m ha
            unfold t
            rfl
        rw [aux3, aux4]
        simp
      _ = n * c + S n ^ 2 := by 
        simp
        have aux1 : ∑ i ∈ Icc 1 (n - 1), (S (i + 1) - S (i - 1)) * S i 
          = ∑ i ∈ Icc 1 (n - 1), (S (i + 1) * S i - S (i - 1) * S i) := by 
          apply sum_congr rfl
          intro i hi
          ring
        -- use the telecopiling method to simplify the equation.
        have aux2 : ∑ i ∈ Icc 1 (n - 1), (S (i + 1) * S i - S (i - 1) * S i) 
          = S n * S (n - 1) - S 1 * S 0 := by
          rw [Finset.sum_sub_distrib]
          have aux3 : ∑ x ∈ Icc 1 (n - 1), S (x + 1) * S x = 
            S n * S (n - 1) + ∑ x ∈ Icc 1 (n - 2), S (x + 1) * S x:= by 
            have this : Icc 1 (n - 1) = insert (n - 1) (Icc 1 (n - 2)) := by
              have eq_aux : n - 1 = n - 2 + 1 := by omega
              rw [eq_aux]
              refine Eq.symm (Nat.Icc_insert_succ_right ?_)
              linarith
            rw [this, sum_insert, show n - 1 + 1 = n by omega]
            simp
            intro hge
            omega
          have aux4 : ∑ x ∈ Icc 1 (n - 1), S (x - 1) * S x
            = ∑ x ∈ Icc 2 (n - 1), S (x - 1) * S x + S 1 * S 0 := by
            have this : Icc 1 (n - 1) = insert 1 (Icc 2 (n - 1)) := by
              refine (erase_eq_iff_eq_insert ?_ ?_).mp ?_
              simp
              omega
              simp
              simp
              exact rfl
            rw [this, sum_insert, show 1 - 1 = 0 by omega]
            ring
            simp
          have aux5 : ∑ x ∈ Icc 1 (n - 2), S (x + 1) * S x
            = ∑ x ∈ Icc 2 (n - 1), S (x - 1) * S x := by
            let t : ℕ → ℕ := fun i => i + 1
            let s : ℕ → ℕ := fun i => i - 1
            refine sum_nbij' t s ?_ ?_ ?_ ?_ ?_
            · simp
              intro x hx1 hx2
              unfold t
              omega
            · simp 
              intro x hx1 hx2
              unfold s
              omega
            · simp
              intro x hx1 hx2
              unfold t s
              omega
            · simp
              intro x hx1 hx2
              unfold t s
              omega
            · intro x hx
              unfold t
              rw [show x + 1 - 1 = x by omega]
              ring
          rw [aux3, aux4, aux5]
          ring
        rw [aux1, aux2, eq1]
        ring
  have eq3 : 1 * (S n * S n) + (-1) * S n + n * c = 0 := by 
    linarith
  have eq4 : n * c = S n - S n ^ 2 := by 
    linarith
  have disge : discrim 1 (-1) (n * c) ≥ 0 := by
    rw [discrim, eq4]
    linarith [sq_nonneg (2 * S n - 1)]
  unfold discrim at disge
  simp at disge
  refine (le_div_iff₀ ?_).mpr ?_
  positivity
  linarith