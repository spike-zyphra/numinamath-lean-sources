import Mathlib

open Real Set
open scoped BigOperators

/- 1. Let $n$ be a positive odd number, and $x_{1}, x_{2}, \cdots, x_{n}$ be non-negative real numbers. Prove:

$$

\min _{i=1,2, \cdots, n}\left\{x_{i}^{2}+x_{i+1}^{2}\right\} \leqslant \max _{j=1,2, \cdots, n}\left\{2 x_{j} x_{j+1}\right\},

$$


where, $x_{n+1}=x_{1}$. -/

-- lemma that in a odd length cyclic sequence there are two consecutive elements of product nonnegative
lemma l_consecutive_same_sign {n : ℕ} [NeZero n] (hn : Odd n) (x : Fin n → ℝ) :
    ∃ i, 0 ≤ (x i) * (x (i + 1)) := by
  -- if not then consecutive product is always negative
  by_contra h
  simp at h
  -- by induction x 0 * x (2 * i + 1) is always negative
  have h2 (i : ℕ) : x 0 * x (2 * i + 1) < 0 := by
    induction' i with m hm
    . specialize h 0
      simpa using h
    . push_cast
      have h2 := h (2 * m + 1)
      have h3 := h (2 * m + 2)
      ring_nf at hm h2 h3 ⊢
      nlinarith
  -- as n is odd it is of form 2*k+1 and we get contradiction
  obtain ⟨k, hk⟩ := hn
  specialize h2 k
  norm_cast at h2
  rw [← hk] at h2
  simp at h2
  ring_nf at h2
  have := sq_nonneg (x 0)
  linarith

-- lemma that if (a - b) * (b - c) is nonegative then a ≤ b ≤ c or c ≤ b ≤ a
lemma l_chain_of_mul_nonpos (a b c : ℝ) (h : 0 ≤ (a - b) * (b - c)) : (a ≤ b ∧ b ≤ c) ∨
    (c ≤ b ∧ b ≤ a) := by
  -- wlog a ≤ b as if not then we can apply result on c b a
  wlog hab : a ≤ b
  . specialize this c b a (by linarith) (by nlinarith)
    revert this
    tauto
  -- if a = b, then b ≤ c or c ≤ b is goal, which is obvious
  by_cases hab' : a = b
  . simp [hab']
    exact le_total b c
  -- otherwise a < b and then b - c ≤ 0 obviously
  . left
    simp [hab]
    replace hab' : a < b := lt_of_le_of_ne hab hab'
    nlinarith

-- if a ≤ b ≤ c then a^2 + b^2 ≤ 2 * b^2 ≤ 2 * b *c
lemma l_ineq_of_chain {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hac : b ≤ c) :
    a^2 + b^2 ≤ 2 * b * c := by
  calc
    _ ≤ b^2 + b^2 := by gcongr
    _ = 2 * b * b := by ring
    _ ≤ 2 * b * c := by gcongr

theorem inequalities_153535 {n : ℕ} [NeZero n] (hn : Odd n) (x : Fin n → ℝ)
  (hx : ∀ i, 0 ≤ x i) : (Finset.univ.image (fun i ↦ (x i)^2 + x (i + 1)^2)).min' (by simp) ≤
  (Finset.univ.image (fun i ↦ 2 * (x i) * x (i + 1))).max' (by simp) := by
  -- first we prove that proving inequality for some i in left side and some j in right side is ok, as min left ≤ left(some i) ≤ right(some j) ≤ max right
  suffices ∃ i j, (x i)^2 + x (i + 1)^2 ≤ 2 * x j * x (j + 1) by
    obtain ⟨i, j, hij⟩ := this
    calc
      _ ≤ (x i)^2 + x (i + 1)^2 := by
        apply Finset.min'_le
        simp
      _ ≤ 2 * x j * x (j + 1) := hij
      _ ≤ _ := by
        apply Finset.le_max'
        simp
  -- by first lemma there are consecutive x (i + 1) - x that have nonnegative product
  obtain ⟨i, hi⟩ := l_consecutive_same_sign hn (fun i ↦ x (i + 1) - x i)
  -- then by second lemma three elements are nondecreasing or nonincreasing, in both cases by third lemma we get required inequalities
  obtain h | h := l_chain_of_mul_nonpos (x (i + 1 + 1)) (x (i + 1)) (x i) (by linarith)
  . have := l_ineq_of_chain (hx _) (hx _) h.left h.right
    use i + 1, i
    linarith
  . have := l_ineq_of_chain (hx _) (hx _) h.left h.right
    use i, i + 1