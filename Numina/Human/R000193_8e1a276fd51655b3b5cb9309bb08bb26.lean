import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Determine, whether exists function  $f$ , which assigns each integer  $k$ ,
nonnegative integer  $f(k)$  and meets the conditions: $f(0) > 0$ ,
for each integer  $k$  minimal number of the form  $f(k - l) + f(l)$ ,
where  $l \in \mathbb{Z}$ , equals  $f(k)$ .-/
theorem number_theory_8528 :
  ¬ ∃ f : ℤ → ℕ, f 0 > 0 ∧ ∀ k, IsLeast {x | ∃ l, x = f (k - l) + f l} (f k) := by
  -- Natural numbers are well founded.
  have min_of_nat_set {s : Set ℕ} (hs : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
    use Nat.lt_wfRel.wf.min s hs
    constructor
    . apply WellFounded.min_mem
    intro y hy
    apply WellFounded.min_le
    exact hy
  push_neg
  intro f hf0
  by_contra hk
  push_neg at hk
  -- We can deduce f(x+y)≤f(x)+f(y) from f(k)=min{f(k-l)+f(l)}
  have h1 (x y) : f (x + y) ≤ f x + f y := by
    specialize hk (x + y)
    unfold IsLeast lowerBounds at hk
    have := hk.2
    simp at this
    convert this y
    ring
  -- As f(x)=min{f(x-l)+f(l)}, there exists y such that f(x)=f(x-y)+f(y).
  have h2 x : ∃ y, f x = f (x - y) + f y := by
    specialize hk x
    unfold IsLeast at hk
    exact hk.1
  -- Let m be the minimum of f(x).
  have : (Set.range f).Nonempty := by use f 0; simp
  obtain ⟨m, hm⟩ := min_of_nat_set this
  -- There exists u such that f(u)=m.
  obtain ⟨u, hu⟩ := hm.1
  -- There exists v such that f(u)=f(u-v)+f(v)
  obtain ⟨v, hv⟩ := h2 u
  -- Notice that m is the minimum of f(x), we have f(u-v),f(v) ≤ m.
  have := hm.2 (f v) (by simp)
  have := hm.2 (f (u - v)) (by simp)
  -- Further, we can deduce m=0 from f(u-v)+f(v)=m ≤ m+m.
  have : m + m ≤ f (u - v) + f v := by linarith
  rw [← hv, hu] at this
  have : m = 0 := by omega
  -- Let A be the set of x such that f(x)=0.
  set A : Set ℤ := {x | f x = 0}
  -- Clearly, 0 is not in A.
  have zero_not_mem_A : 0 ∉ A := hf0.ne'
  -- If x,y are in A, same is x+y.
  have add_mem_A {x y} (hx : x ∈ A) (hy : y ∈ A) : x + y ∈ A := by
    specialize h1 x y
    rw [hx, hy, Nat.add_zero] at h1
    rw [Nat.le_zero_eq] at h1
    exact h1
  -- If x is in A, same is (s+1)x where s is a natural number.
  have smul_mem_A (s : ℕ) {x} (hx : x ∈ A) : (s + 1) * x ∈ A := by
    induction' s with s ih
    . simpa
    rw [add_mul, one_mul]
    exact add_mem_A ih hx
  set Aplus : Set ℕ := {x | f x = 0} with hAplus
  set Aminus : Set ℕ := {x | f (-x) = 0} with hAminus
  have mem_Aminus_of_nonpos {x} (hx : x ≤ 0) (hfx : f x = 0) : x.natAbs ∈ Aminus := by
    simp [hAminus]
    convert hfx
    rw [abs_of_nonpos hx, neg_neg]
  have mem_Aplus_of_pos {x} (hx : 0 < x) (hfx : f x = 0) : x.natAbs ∈ Aplus := by
    simp [hAplus]
    convert hfx
    rw [abs_of_pos hx]
  -- If all elements of A are positive, there is a contradiction.
  rcases Aminus.eq_empty_or_nonempty with ham | ham
  . have hap : Aplus.Nonempty := by
      have hfu : f u = 0 := by rw [hu, this]
      use u.natAbs
      simp [hAplus]
      rw [abs_of_pos, hfu]
      by_contra h
      push_neg at h
      have := mem_Aminus_of_nonpos h hfu
      simp [ham] at this
    obtain ⟨a, ha⟩ := min_of_nat_set hap
    have pos_of_lt_a {x} (hx : x < (a : ℤ)) : 0 < f x  := by
      rw [Nat.pos_iff_ne_zero]
      by_contra hfx
      rcases lt_trichotomy x 0 with h | h | h
      . have : x.natAbs ∈ Aminus := by
          apply mem_Aminus_of_nonpos
          . exact h.le
          . exact hfx
        simp [ham] at this
      . simp [← h, hfx] at hf0
      . have := ha.2 _ (mem_Aplus_of_pos h hfx)
        zify at this
        rw [abs_of_pos h] at this
        linarith
    obtain ⟨y, hy⟩ := h2 a
    rw [ha.1, eq_comm] at hy
    replace hy := Nat.eq_zero_of_add_eq_zero hy
    rcases lt_or_le 0 y with h | h
    have : f (a - y) ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero]
      apply pos_of_lt_a
      linarith
    exact this hy.1
    have := mem_Aminus_of_nonpos h hy.2
    simp [ham] at this
  -- If all elements of A are negtive, there is also a contradiction.
  rcases Aplus.eq_empty_or_nonempty with hap | hap
  . obtain ⟨b, hb⟩ := min_of_nat_set ham
    have pos_of_gt_b {x} (hx : x > (-b : ℤ)) : 0 < f x := by
      rw [Nat.pos_iff_ne_zero]
      by_contra hfx
      rcases lt_trichotomy x 0 with h | h | h
      . have := hb.2 _ (mem_Aminus_of_nonpos (by linarith) hfx)
        zify at this
        rw [abs_of_neg (by linarith)] at this
        linarith
      . simp [← h, hfx] at hf0
      . have := mem_Aplus_of_pos h hfx
        simp [hap] at this
    obtain ⟨y, hy⟩ := h2 (-b)
    rw [hb.1, eq_comm] at hy
    replace hy := Nat.eq_zero_of_add_eq_zero hy
    rcases lt_or_le y 0 with h | h
    have : f (-b-y) ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero]
      apply pos_of_gt_b
      linarith
    exact this hy.1
    rcases eq_or_ne y 0 with hy0 | hy0
    . have : 0 > 0 := by nth_rw 1 [← hy.2]; rwa [hy0]
      contradiction
    have : 0 < y := by omega
    have := mem_Aplus_of_pos this hy.2
    simp [hap] at this
  -- Choose a to be the min positive element in A.
  -- Choose b to be the max negtive element in A.
  obtain ⟨a, ha⟩ := min_of_nat_set hap
  obtain ⟨b, hb⟩ := min_of_nat_set ham
  have ha_mem_A : (a : ℤ) ∈ A := ha.1
  have hb_mem_A : (-b : ℤ) ∈ A := hb.1
  have hapos : 0 < (a : ℤ) := by
    norm_cast
    rw [Nat.pos_iff_ne_zero]
    intro h
    rw [h] at ha_mem_A
    contradiction
  have hbpos : 0 < (b : ℤ) := by
    norm_cast
    rw [Nat.pos_iff_ne_zero]
    intro h
    rw [h] at hb_mem_A
    contradiction
  -- Use Bezout's indentity, there exists x,y such that xa+yb=gcd(a,b).
  have bezout_identity (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = Int.gcd a b := by
    use Int.gcdA a b, Int.gcdB a b
    symm
    convert Int.gcd_eq_gcd_ab a (b) using 1
    ac_rfl
  -- Further there exists postivie integer m,n such that ma-nb=gcd(a,b).
  have hmn : ∃ (m n : ℕ), (m + 1) * a + (n + 1) * (-b : ℤ) = Int.gcd a b := by
    obtain ⟨x, y, hxy⟩ := bezout_identity a b
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < x + n * b ∧ y - n * a < 0 := by
      obtain ⟨n1, hn1⟩ := Archimedean.arch (-x + 1) hbpos
      obtain ⟨n2, hn2⟩ := Archimedean.arch (y + 1) hapos
      use max n1 n2
      constructor
      . have : n1 * (b : ℤ) ≤ max n1 n2 * b := by
          refine Int.mul_le_mul_of_nonneg_right ?_ hbpos.le
          norm_cast
          exact Nat.le_max_left n1 n2
        simp at hn1
        linarith
      have : n2 * (a : ℤ) ≤ max n1 n2 * a := by
        refine Int.mul_le_mul_of_nonneg_right ?_ hapos.le
        norm_cast
        exact Nat.le_max_right n1 n2
      simp at hn2
      linarith
    have : (x + n*b)*a + (n*a - y)*(-b)= Int.gcd a b := by linear_combination hxy
    use (x + n*b - 1).natAbs, (n*a - y - 1).natAbs
    zify
    repeat rw [abs_of_nonneg (by linarith)]
    linear_combination this
  -- There exists positive integer p,q such that pa-qb=-gcd(a,b).
  have hpq : ∃ (p q : ℕ), (p + 1) * a + (q + 1) * (-b : ℤ) = -Int.gcd a b := by
    obtain ⟨x, y, hxy⟩ := bezout_identity a b
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x - n * b < 0 ∧ 0 < y + n * a := by
      obtain ⟨n1, hn1⟩ := Archimedean.arch (x + 1) hbpos
      obtain ⟨n2, hn2⟩ := Archimedean.arch (-y + 1) hapos
      use max n1 n2
      constructor
      . have : n1 * (b : ℤ) ≤ max n1 n2 * b := by
          refine Int.mul_le_mul_of_nonneg_right ?_ hbpos.le
          norm_cast
          exact Nat.le_max_left n1 n2
        simp at hn1
        linarith
      have : n2 * (a : ℤ) ≤ max n1 n2 * a := by
        refine Int.mul_le_mul_of_nonneg_right ?_ hapos.le
        norm_cast
        exact Nat.le_max_right n1 n2
      simp at hn2
      linarith
    have : (-x + n*b)*a + (y+n*a)*(-b)= -Int.gcd a b := by linear_combination -hxy
    use (-x + n*b - 1).natAbs, (y+n*a - 1).natAbs
    zify
    repeat rw [abs_of_nonneg (by linarith)]
    linear_combination this
  rcases hmn with ⟨m, n, hmn⟩
  rcases hpq with ⟨p, q, hpq⟩
  -- It is obvious that ma-nb is in A.
  have hmn_mem_A : (m + 1) * a + (n + 1) * (-b : ℤ) ∈ A := by
    apply add_mem_A
    . apply smul_mem_A
      exact ha_mem_A
    . apply smul_mem_A
      exact hb_mem_A
  -- It is obvious that pa-nb is in A.
  have hpq_mem_A : (p + 1) * a + (q + 1) * (-b : ℤ) ∈ A := by
    apply add_mem_A
    . apply smul_mem_A
      exact ha_mem_A
    . apply smul_mem_A
      exact hb_mem_A
  -- Hence 0 = (ma-nb) + (pa-nb) is in A which is a contradiction.
  have := add_mem_A hmn_mem_A hpq_mem_A
  rw [hmn, hpq, ← sub_eq_add_neg, sub_self] at this
  contradiction
