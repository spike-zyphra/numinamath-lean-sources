import Mathlib
namespace number_theory_604323

def nmod (a b:ℕ) := if a % b ≠ 0 then a % b else b

end number_theory_604323
open number_theory_604323

/- The positive integer $k$ and the set $A$ of different integers from 1 to $3 k$ inclusive are such that there are no distinct $a, b, c$ in $A$ satisfying $2 b=a+c$.
The numbers from $A$ in the interval $[1, k]$ will be called small; those in $[k+1,2 k]$ - medium and those in $[2 k+1,3 k]$ - large.
Is it always true that there are no positive integers $x$ and $d$ such that if $x, x+d$ and $x+2 d$ are divided by $3 k$ then the remainders belong to $A$ and those of $x$ and $x+d$ are different and are:
a) small?  b) medium?   c) large?
(In this problem we assume that if a multiple of $3 k$ is divided by $3 k$ then the remainder is $3 k$ rather than 0. ) -/
theorem number_theory_604323_a : ∃ k x d : ℕ , ∃ A : Finset ℕ , (k > 0)∧(A ⊆ Finset.Icc 1 (3 * k)) ∧ (∀ a ∈ A , ∀ b ∈ A ,∀ c ∈ A , a ≠ b → b ≠ c → a ≠ c → 2 * b ≠ a + c) ∧
  (nmod x (3*k)∈A) ∧  (nmod (x+d) (3*k)∈A) ∧ (nmod (x+2*d) (3*k)∈A) ∧ (x % (3 * k) ≠ (x + d) % (3 * k)) ∧ ((1 ≤ x % (3 * k))
  ∧ (x % (3 * k) ≤ k)) ∧ ((1 ≤ (x + d) % (3 * k)) ∧ ((x + d) % (3 * k) ≤ k)) := by
  -- A counterexample for a) is $k=3, A=\{1,2,9\}, x=2$ and $d=8$.
  use 3 ;use 2 ;use 8 ;use {1 ,2 ,9} ;simp [nmod];exact Finset.inter_eq_right.mp rfl

theorem number_theory_604323_c : ∃ k x d : ℕ , ∃ A : Finset ℕ , (k > 0)∧(A ⊆ Finset.Icc 1 (3 * k)) ∧ (∀ a ∈ A , ∀ b ∈ A ,∀ c ∈ A , a ≠ b → b ≠ c → a ≠ c → 2 * b ≠ a + c) ∧
  (nmod x (3*k)∈A) ∧  (nmod (x+d) (3*k)∈A) ∧ (nmod (x+2*d) (3*k)∈A) ∧ (x % (3 * k) ≠ (x + d) % (3 * k)) ∧ ((2 * k + 1 ≤ nmod x (3 * k)) ∧ (nmod x (3 * k) ≤ 3 * k))
  ∧ ((2 * k + 1 ≤ nmod (x + d) (3 * k)) ∧ (nmod (x + d) (3 * k) ≤ 3 * k)) := by
  -- A counterexample for c) is $k=3, A=\{1,8,9\}, x=8$ and $d=1$.
  use 3 ;use 8 ;use 1 ;use {1 ,8 ,9} ;simp [nmod] ;exact Finset.inter_eq_right.mp rfl

-- We will prove that b) is true.
theorem number_theory_604323_b (k : ℕ) (A : Finset ℕ) (hk : k > 0) (hA : A ⊆ Finset.Icc 1 (3 * k)) (hAmem : ∀ a ∈ A , ∀ b ∈ A ,∀ c ∈ A , a ≠ b → b ≠ c → a ≠ c → 2 * b ≠ a + c) :
  ¬∃ x d : ℕ , (nmod x (3 * k)  ∈ A) ∧  (nmod (x + d) (3 * k) ∈ A) ∧ (nmod (x + 2 * d) (3 * k) ∈ A) ∧ (x % (3 * k) ≠ (x + d) % (3 * k)) ∧
  ((k + 1 ≤ x % (3 * k)) ∧ (x % (3 * k) ≤ 2 * k)) ∧ ((k + 1 ≤ (x + d) % (3 * k)) ∧ ((x + d) % (3 * k) ≤ 2 * k)) := by
  -- Suppose the contrary and let $x, d$ have the above properties.
  by_contra!
  rcases this with ⟨x ,d ,hx ,hxd ,hx2d ,hx_xd ,hx_range ,hxd_range⟩
  -- We can assume $k < x \le 2k$ and let $ d' = (x + d) \% 3k - x $,
  let x' : ℤ := x % (3 * k)
  let d' : ℤ := (x + d) % (3 * k) - x'
  have hx'_range : ↑(k+1) ≤ x' ∧ x' ≤ ↑(2 * k) := by
    constructor
    · apply Nat.cast_le.mpr ;exact hx_range.1
    apply Nat.cast_le.mpr ;exact hx_range.2
  -- , then since the remainder for $x+d$ is medium we have $k < x+d' \le 2k$.
  have hx'd' : x' + d' = ↑((x + d) % (3 * k)) := by simp [x',d']
  have hxd'_range : ↑(k + 1) ≤ x' + d' ∧ x' + d' ≤ ↑(2 * k) := by
    rw [hx'd']
    constructor
    · apply Nat.cast_le.mpr ;exact hxd_range.1
    apply Nat.cast_le.mpr ;exact hxd_range.2
  -- Therefore $-k < d' = (x+d)\%3k- x < k$.
  have hd'_range : -↑k < d' ∧ d' < ↑k := by
    have : d' = (x' + d') - x' := by ring
    constructor
    · have : ↑(k + 1) - ↑(2 * k) ≤ d' := by rw[this] ;linarith
      have eq : ↑(k + 1) - ↑(2 * k) = -(↑k :ℤ)+1 := by simp [two_mul] ;rw [add_comm,sub_eq_add_neg]
      rw [eq] at this ;linarith
    have : d' ≤ ↑(2 * k) - ↑(k + 1) := by rw[this] ;linarith
    have eq : ↑(2 * k) - ↑(k + 1) = (↑k :ℤ)-1 := by simp [two_mul]
    rw [eq] at this ;linarith
  -- Hence $0 < x+2d' = (x+d') + d' < 3k$.
  have hx2d'_range : ↑1 ≤ x' + 2 * d' ∧ x' + 2 * d' < ↑(3 * k) := by
    have : x' + 2 * d' = (x' + d') + d' := by ring
    constructor
    · have : ↑(k + 1) + (-↑k) ≤ x' + 2 * d' := by rw [this] ;linarith
      have eq : ↑(k + 1) + (-↑k : ℤ) = ↑1 := by simp
      rw [eq] at this ;exact this
    have : x' + 2 * d' < ↑(2 * k) + ↑(k) := by rw [this] ;linarith
    have eq : ↑(2 * k) + (↑k : ℤ ) = ↑(3 * k) := by simp ;ring
    rw [eq] at this ;exact this
  -- Thus $x+2d' = (x+2d)\%3k$
  have hx2d'_eq: (x + 2 * d) % (3 * k) = (x' + 2 * d') % (3 * k) := by
    simp [x',d']
    nth_rewrite 2 [Int.add_emod]
    rw [Int.mul_emod,← Int.sub_emod,← Int.mul_emod,← Int.add_emod]
    ring_nf
  have : (x' + 2 * d') % (3 * k) = x' + 2 * d' := by
    refine Int.emod_eq_of_lt (by linarith) ?_
    have : 3 * (↑k : ℤ) = ↑(3 * k) := rfl
    rw [this] ;exact hx2d'_range.2
  rw [this] at hx2d'_eq
  -- and the remainders $x, x+d'$ and $x+2d'$ are in $A$ and $ 2(x+d') = (x+2d') + x $
  have heq : 2 * (x' + d') = x' + (x' + 2 * d') := by ring
  rw [hx'd',← hx2d'_eq] at heq
  simp only [x'] at heq
  have h1 : (2 * ((x + d) % (3 * k))) = x % (3 * k) + (x + 2 * d) % (3 * k) := by exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm heq)))
  -- a contradiction.
  have h2 :  2 * ((x + d) % (3 * k)) ≠ x % (3 * k) + (x + 2 * d) % (3 * k) := by
    apply hAmem
    · have : x % (3 * k) ≠ 0 := by linarith
      have : nmod x (3 * k) = x % (3 * k) := by simp [nmod,this]
      rw [this] at hx ;exact hx
    · have : (x + d) % (3 * k) ≠ 0 := by linarith
      have : nmod (x + d) (3 * k) = (x + d) % (3 * k) := by simp [nmod,this]
      rw [this] at hxd ;exact hxd
    · have : (x + 2 * d) % (3 * k) ≠ 0 := by linarith
      have : nmod (x + 2 * d) (3 * k) = (x + 2 * d) % (3 * k) := by simp [nmod,this]
      rw [this] at hx2d ;exact hx2d
    · exact hx_xd
    · contrapose! hx_xd
      symm at hx_xd
      apply Nat.sub_mod_eq_zero_of_mod_eq at hx_xd
      have : x + 2 * d - (x + d) = d := by simp [two_mul,← add_assoc]
      rw [this] at hx_xd
      rw [Nat.add_mod,hx_xd] ;simp
    contrapose! hx_xd
    rw [← hx_xd,← two_mul] at h1
    simp at h1
    apply Nat.sub_mod_eq_zero_of_mod_eq at h1
    have : x + d - x = d := by simp
    rw [this] at h1
    rw [Nat.add_mod,h1] ;simp
  exact h2 h1