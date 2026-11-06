import Mathlib

open BigOperators


/-
3. [4] Find the smallest positive integer $n$ such that $\underbrace{2^{2 \cdot}}_{n}>3^{3^{3^{3}}}$. (The notation $\underbrace{2^{2 \cdot \cdot}}_{n}$ is used to denote a power tower with $n 2$ 's. For example, $\underbrace{2^{2^{2}}}_{n}$ with $n=4$ would equal $2^{2^{2^{2}}}$.)
-/


--We first have lemma about the exact value of a n.
lemma l0 (a : ℕ → ℕ) (h1 : a 1 = 2) (ha: ∀n≥1, a (n+1) = 2^(a n)):
a 4 = (2^(2^(2^2))) := by
  simp [ha, h1]
lemma l1 (a : ℕ → ℕ) (h1 : a 1 = 2) (ha: ∀n≥1, a (n+1) = 2^(a n)):
a 5 = 2^(2^(2^(2^2))) := by 
  have ha4: a 4 = (2^(2^(2^2))) := by apply l0; exact h1; exact ha
  rw [← ha4]
  apply ha
  norm_num
lemma l2 (a : ℕ → ℕ) (h1 : a 1 = 2) (ha: ∀n≥1, a (n+1) = 2^(a n)):
a 6 = 2^(2^(2^(2^(2^2)))) := by 
  have t1 : a 5 = 2^(2^(2^(2^2))) := by apply l1; exact h1; exact ha
  specialize ha 5 (by norm_num)
  simp at ha
  rw [t1] at ha
  exact ha

--a is increasing.
lemma l3 (a : ℕ → ℕ) (ha: ∀n≥1, a (n+1) = 2^(a n)):
MonotoneOn a (Set.Ici 1) := by 

  have cla : ∀k:ℕ, ∀x:ℕ, ∀y:ℕ, (1 ≤ x ∧ x ≤ y ∧ y - x = k) → a x ≤ a y := by
    intro k
    induction' k with k indk

    intro x y h
    obtain ⟨xge1,xley,ymxe0⟩ := h
    have : x = y := by omega
    rw [this]

    intro x y h
    obtain ⟨xge1,xley,ymxekp1⟩ := h
    specialize indk x (x+k)
    simp [xge1] at indk
    have ye : y = x + (k+1) := by omega
    rw [ye]
    have cla : a (x + k) ≤ a (x + (k+1)) := by 
      specialize ha (x+k)
      simp at ha
      have : 1 ≤ x + k := by omega
      simp [this] at ha
      have : x + (k+1) = x + k + 1 := by ring
      rw [this]
      rw [ha]
      have : a (x + k) < 2 ^ a (x + k) := by apply Nat.lt_pow_self; norm_num
      linarith
    linarith
  unfold MonotoneOn
  intro x rx y ry xley
  simp at rx ry
  apply cla
  constructor
  exact rx
  constructor
  exact xley
  have : y - x = y - x := by rfl
  exact this

lemma l4:
2^(2^(2^(2^2))) = 2 ^ (2^16) := by 
  have : 2^(2^2) = 16 := by norm_num
  rw [this]

--Now, we show that n = 5 is now enough while n = 6 is.
lemma l5:
2^(2^(2^(2^(2^2)))) = 2 ^ (2^(2^16)) := by 
  rw [l4]
lemma l6:
3^(3^(3^3)) = 3^(3^27) := by 
  have : 3^3 = 27 := by norm_num
  rw [this]
lemma l7 :
2^(2^(2^(2^2))) ≤ 3^(3^(3^3)) := by
  rw [l4,l6]
  gcongr <;> norm_num
lemma l8 :
3^(3^(3^3)) < 2^(2^(2^(2^(2^2)))) := by 
  rw [l5,l6]
  
  have t0 : (4^4^(27)) = 2^(2^55) := by
    have : 4 = 2^2 := by norm_num
    nth_rw 1 [this]
    rw [← pow_mul]
    rw [this]
    rw [← pow_mul]
    have : 2*27 = 54 := by norm_num
    rw [this]
    have : 2 ^ 55 = 2*2^54 := by
      have : 55 = 54 + 1 := by ring
      rw [this]
      rw [pow_succ]
      rw [mul_comm]
    rw [this]

  have t1 : 3 ^ 3 ^ 27 ≤ 2^(2^16) * (4^4^(27)) := by 
    have a1 : 1 ≤ 2 ^ 2 ^ 16 := by 
      apply Nat.one_le_pow
      norm_num
    have a2 : 3 ^ 3 ^ 27 ≤ 4^4^(27) := by 
      gcongr <;> norm_num
    have a3 : 1 * (3 ^ 3 ^ 27) ≤ 2 ^ 2 ^ 16 * 4 ^ 4 ^ 27 :=by
      gcongr 
    have : 1 * (3 ^ 3 ^ 27) = (3 ^ 3 ^ 27) := by 
      let t := (3 ^ 3 ^ 27)
      have : 1 * t = t := by rw [one_mul]
      simp only [t] at this
      exact this
    rw [this] at a3
    exact a3

  have t2 : 2^(2^16) * (4^4^(27)) ≤ 2^(2^(100)) := by 
    rw [t0]
    rw [← pow_add]
    gcongr
    norm_num
    have a1 : 2^16 ≤ 2^55 := by gcongr <;> norm_num
    have a2 : 2^16 + 2^55 ≤ 2^55 + 2^55 := by 
      gcongr
    have a3 : 2^55 + 2^55 ≤ 2^100 := by 
      rw [← mul_two]
      rw [← pow_succ]
      gcongr <;> norm_num
    apply le_trans a2 a3

  have t3 : 2^(2^(100)) < 2 ^ 2 ^ 2 ^ 16 := by 
    gcongr <;> norm_num

  have : 3 ^ 3 ^ 27 ≤ 2 ^ 2 ^ 100 := by
    apply le_trans
    exact t1
    exact t2
    
  apply lt_of_le_of_lt
  exact this
  exact t3



theorem number_theory_161938 (a : ℕ → ℕ) (h1 : a 1 = 2) (ha: ∀n≥1, a (n+1) = 2^(a n)):
IsLeast {n : ℕ | 0 < n ∧ (a n) > 3^(3^(3^3))} 6 := by 

  --We simply apply the lemmas.
  unfold IsLeast lowerBounds
  simp only [gt_iff_lt, Set.mem_setOf_eq, true_and, and_imp]

  constructor

  --6 layers is enough.
  have ha6 : a 6 = 2^(2^(2^(2^(2^2)))) := by apply l2; exact h1; exact ha
  rw [ha6]
  constructor
  norm_num
  apply l8



  --5 layers is not enough
  have ha5 : a 5 = (2^(2^(2^(2^2)))) := by apply l1; exact h1; exact ha
  intro n npos h
  by_contra nnge6
  have : n ≤ 5 := by 
    linarith
  have lea5 : a n ≤ a 5 := by 
    apply l3; exact ha; 
    simp; linarith
    simp
    exact this
  have a5le : a 5 ≤ 3^(3^(3^3)) := by 
    rw [ha5]
    apply l7
  have : 3^(3^(3^3)) < a 5 := by apply lt_of_lt_of_le; exact h; exact lea5
  have : ¬ a 5 ≤ 3^(3^(3^3)) := by push_neg; exact this
  apply this
  exact a5le