import Mathlib

open Finset Complex

/- Given a positive [integer](https://artofproblemsolving.com/wiki/index.php/Integer) $n$, it can be shown that every [complex number](https://artofproblemsolving.com/wiki/index.php/Complex_number) of the form $r+si$, where $r$ and $s$ are integers, can be uniquely expressed in the base $-n+i$ using the integers $0,1,2,\ldots,n^2$ as digits. That is, the equation

$r+si=a_m(-n+i)^m+a_{m-1}(-n+i)^{m-1}+\cdots +a_1(-n+i)+a_0$
is true for a unique choice of non-negative integer $m$ and digits $a_0,a_1,\ldots,a_m$ chosen from the set $\{0,1,2,\ldots,n^2\}$, with $a_m\ne 0$. We write

$r+si=(a_ma_{m-1}\ldots a_1a_0)_{-n+i}$
to denote the base $-n+i$ expansion of $r+si$. There are only finitely many integers $k+0i$ that have four-digit expansions

$k=(a_3a_2a_1a_0)_{-3+i}~~$   $~~a_3\ne 0.$
Find the sum of all such $k$, -/
theorem number_theory_95455 :
    ∑ᶠ k ∈ {k : ℤ | ∃ a : ℕ → ℕ, a 3 ≠ 0 ∧ k = (∑ i ∈ range 4, a i * (-3 + I) ^ i) ∧
      ∀ i ∈ range 4, a i ∈ Icc 0 (3 ^ 2)}, k = 490 := by
  have hi3 : I ^ 3 = -I := by rw [pow_three]; norm_num
  -- show that when an integer k is written with 4 digits in base -3 + I
  -- then k = 292x_{-3 + I} or k = 154x_{-3 + I}
  have h {k : ℤ} {a : ℕ → ℕ} (ha : a 3 ≠ 0) (har : ∀ i < 4, a i ≤ 9)
      (hk : k = (∑ i ∈ range 4, a i * (-3 + I) ^ i)) :
      a 1 = 2 ∧ a 2 = 9 ∧ a 3 = 2 ∨ a 1 = 4 ∧ a 2 = 5 ∧ a 3 = 1 := by
    -- the imaginary part of k is 0
    -- so we get 26 * a 3 - 6 * a 2 + a 1 = 0
    apply_fun Complex.im at hk
    simp [Finset.sum] at hk
    ring_nf at hk
    field_simp [show I ^ 3 = -I by rw [pow_three]; norm_num] at hk
    norm_num at hk
    norm_cast at hk
    have h1 := har 1 (by norm_num)
    have h2 := har 2 (by norm_num)
    have h3 := har 3 (by norm_num)
    simp at h1 h2 h3
    -- 0 ≤ a 1, a 2, a 3 ≤ 9 and we find that the only possible values
    -- of a 3 are a 3 = 1 and a 3 = 2
    cases' show a 3 = 1 ∨ a 3 = 2 by omega with h h <;> simp [h] at hk
    · right
      omega
    · left
      omega
  -- let s be the set of all integers k from the theorem statement
  set s := {k : ℤ | ∃ a, _}
  -- show that s = {k + 30 | k ∈ [0, 9]} ∪ {k + 10 | k ∈ [0, 9]}
  have heq : s = ((30 + ·) '' Ico (0 : ℤ) 10) ∪ ((10 + ·) '' Ico (0 : ℤ) 10) := by
    ext k
    simp [s]
    constructor
    · intro ⟨a, ha, hk, ha2⟩
      -- assume that k = a_3 a_2 a_1 a_0 in the base -3 + I
      -- then we already proved that k = 292x or k = 154x
      replace h := h ha ha2 hk
      simp [Finset.sum] at hk
      -- it is now easy to derive that 30 ≤ k ≤ 39 or 10 ≤ k ≤ 19
      cases' h with h h
      all_goals {
        simp [h] at hk
        ring_nf at hk
        field_simp [hi3] at hk
        ring_nf at hk
        norm_cast at hk
        have h0 := ha2 0 (by norm_num)
        omega
      }
    · intro h
      -- assume that 30 ≤ k ≤ 39 or 10 ≤ k ≤ 19
      -- and show that it can be written in the form a_3 a_2 a_1 a_0
      -- in the base -3 + I with a_3 ≠ 0
      cases' h with h h <;> lift k to ℕ using by omega
      -- if 30 ≤ k ≤ 39 then set a 0 = k - 30, a 1 = 2, a 2 = 9, and a 3 = 2
      · use fun n => if n = 0 then k - 30 else if n = 1 then 2 else if n = 2 then 9 else 2
        simp [Finset.sum]
        norm_cast at h
        push_cast [h]
        constructor
        · ring_nf
          field_simp [hi3]
        · intro i hi
          interval_cases i <;> simp
          omega
      -- if 10 ≤ k ≤ 19 then set a 0 = k - 10, a 1 = 4, a 2 = 5, and a 3 = 1
      · use fun n => if n = 0 then k - 10 else if n = 1 then 4 else if n = 2 then 5 else 1
        simp [Finset.sum]
        norm_cast at h
        push_cast [h]
        constructor
        · ring_nf
          field_simp [hi3]
        · intro i hi
          interval_cases i <;> simp
          omega
  rw [heq, finsum_mem_eq_toFinset_sum]
  simp
  -- it is left to show that ∑ i ∈ Ico 30 40 ∪ Ico 10 20 = 490
  rw [Finset.sum_union <| disjoint_iff_inter_eq_empty.mpr rfl]
  rw [show ∑ x ∈ Ico (30 : ℤ) 40, x = ∑ x ∈ Ico (30 : ℕ) 40, x by rfl]
  rw [show ∑ x ∈ Ico (10 : ℤ) 20, x = ∑ x ∈ Ico (10 : ℕ) 20, x by rfl]
  simp_rw [Finset.sum_Ico_eq_sum_range]
  rw [sum_add_distrib, sum_add_distrib]
  simp_rw [Finset.sum_range_id, sum_const]
  norm_num