import Mathlib

/-
Let $k$ be a positive integer. A natural number $n$ is said to be a "k-rounded number" if it satisfies $100 \le n < 200$ and the condition $\lfloor 3n/100 \rfloor = \lfloor n/100 \rfloor + k$.
Show that the set of "k-rounded numbers" consists of all integers $n$ such that $\max(100, \lceil 100(k+1)/3 \rceil) \le n \le \min(199, \lceil 100(k+2)/3 \rceil - 1)$.
For example, if $k=4$, the set of "k-rounded numbers" is $\{167, 168, \ldots, 199\}$. If $k=1$ or $k=5$, the set is empty.
-/

--Lemma about the value of ⌊n/100⌋.
lemma l1 (n:ℤ) (nl : 100 ≤ n) (nu : n < 200):
⌊(n / 100 : ℝ)⌋ = 1 := by 
  rw [Int.floor_eq_iff]
  constructor <;> field_simp
  refine (one_le_div₀ ?_).mpr ?_
  norm_num
  norm_cast
  refine (div_lt_iff₀' ?_).mpr ?_
  simp
  norm_cast


--Lemma about the value of ⌊3 * (n:ℝ) / 100⌋.
lemma l2 (n a : ℤ):
⌊3 * (n:ℝ) / 100⌋ = a
↔
⌈100 * (a:ℝ) / 3⌉ ≤ n ∧ n ≤ ⌈100 * ((a:ℝ)+1) / 3⌉ - 1 := by
  rw [Int.floor_eq_iff]
  rw [Int.ceil_le]

  constructor <;> intro h <;> obtain ⟨h1,h2⟩ := h

  constructor
  nlinarith
  refine Int.le_sub_one_of_lt ?_
  rw [Int.lt_ceil]
  nlinarith
  

  constructor
  nlinarith
  have t1 : ⌈100 * ((a:ℝ) + 1) / 3⌉ - 1 < 100 * ((a:ℝ) + 1) / 3 := by 
    refine Int.le_ceil_iff.mp ?_
    linarith
  have t2 : n < 100 * ((a:ℝ) + 1) / 3 := by
    rify at h2
    linarith
  nlinarith


theorem number_theory_638666 (k n:ℤ) (kpos : 0 < k):
100 ≤ n ∧ n < 200 ∧ ⌊(3 * n / 100 : ℝ)⌋ = ⌊(n / 100 : ℝ)⌋ + k 
↔
(max (100:ℝ) (⌈(100 * ((k:ℝ) + 1) / 3)⌉)) ≤ n ∧ n ≤ min (199:ℝ) (⌈100 * ((k:ℝ) + 2) / 3⌉-1) := by
  
  rw [max_le_iff, le_min_iff]
  simp
  have t2 := by apply l2 n (1+k)

  --We apply the lemmas. The remaning part is simple verification.
  constructor <;> intro h
  
  --From left to right.
  obtain ⟨nl,nu,h⟩ := h
  have t1 := by apply l1 n nl nu
  rw [t1] at h
  rw [t2] at h
  field_simp at h ⊢
  ring_nf at h ⊢
  obtain ⟨h1,h2⟩ := h
  constructor
  constructor
  norm_cast
  exact h1
  constructor
  norm_cast; linarith
  norm_cast

  --From right to left.
  obtain ⟨hl,hr⟩ := h
  obtain ⟨h1,h2⟩ := hl
  obtain ⟨h3,h4⟩ := hr
  
  have nl: 100 ≤ n := by rify; exact h1
  have nu: n < 200 := by rify; linarith
  simp [nl,nu]


  have t1 : ⌊(n:ℝ)/100⌋ = 1 := by apply l1 n nl nu
  rw [t1]
  rw [t2]
  field_simp at h2 h4 ⊢
  ring_nf at h2 h4 ⊢
  constructor
  exact h2
  norm_cast at h4
