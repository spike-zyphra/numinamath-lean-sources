import Mathlib

/- definition of friendly number -/
def friendly (a : ℤ) : Prop := ∃ m n : ℤ, m > 0 ∧ n > 0 ∧ (m^2 + n) * (n^2 + m) = a * (m - n)^3


/- a) Prove that there are at least $500$ `friendly` integers in the set $\{1,2,⋯,2012\}$. -/
theorem number_theory_N4_1 : ∃ (S : Finset ℤ), 500 ≤ S.card ∧ ∀ s ∈ S, 0 < s ∧ s <= 2012 ∧ friendly s := by
  /-
  Every $a$ of the form $a=4 k-3$ with $k \geq 2$ is friendly.
  -/
  have N4_a_lemma : ∀ k : ℤ, k ≥ 2 → friendly (4 * k - 3) := by
    intro k hk
    use 2 * k - 1
    use k - 1
    constructor; linarith
    constructor; linarith
    ring
  /-
  Indeed the numbers $m=2 k-1>0$ and $n=k-1>0$ satisfy the given equation with $a=4 k-3$ :  $$ \left(m^{2}+n\right)\left(n^{2}+m\right)=\left((2 k-1)^{2}+(k-1)\right)\left((k-1)^{2}+(2 k-1)\right)=(4 k-3) k^{3}=a(m-n)^{3} \text {. } $$  Hence $5,9, \ldots, 2009$ are friendly and so $\{1,2, \ldots, 2012\}$ contains at least 502 friendly numbers.
  -/
  let f := λ k : ℕ => 4 * (k+2:ℤ) - 3
  have inj_f : Function.Injective f := fun i j h => by
    unfold_let f at h
    simp at h; exact h
  let emb_f := Function.Embedding.mk f inj_f
  -- use a `Finset.map` to build a set of `friendly` numbers constructed by $f = 4(k+2) - 3$
  use ((Finset.range 501).map emb_f)
  constructor
  · -- use tactic to show the constructed set has at least $500$ elements
    aesop
  -- show that the constructed set satisfies the constraints $0 < s$, $s <= 2012$, and is `friendly`.
  intro s hs
  -- use definition to prove the constraints
  simp at hs
  rcases hs with ⟨hs1, hs2, hs3⟩
  unfold_let at hs3
  simp at hs3
  repeat (constructor; linarith)
  -- use the lemma to prove s has the `friendly` property
  rw [← hs3]
  apply N4_a_lemma; linarith


/- b) Proof that $a = 2$ is not `friendly`. -/
theorem number_theory_N4_2 : ¬ friendly 2 := by
  unfold friendly
  -- transform the proposition to ∀ form
  push_neg
  intro m n hm hn h
  -- try to find a contradiction by analyzing the equation
  -- proof that $m > n$
  have : m > n := by
    -- use `mul_pos`, `add_pos` to show that the left side of the equation is positive
    have : (m ^ 2 + n) * (n ^ 2 + m) > 0 := by
      apply mul_pos
      refine add_pos (sq_pos_of_pos hm) hn
      refine add_pos (sq_pos_of_pos hn) hm
    -- then the right side of the equation is also positive
    rw [h] at this
    -- use `lt_of_nsmul_lt_nsmul_right` to show that $(m - n)^3 > 0$
    have : (m - n)^3 > 0 := by
      exact lt_of_nsmul_lt_nsmul_right 2 this
    -- use `Odd.pow_pos_iff` to show that $m - n > 0$
    have o3: Odd 3 := by trivial
    have m_sub_n_pos := (Odd.pow_pos_iff o3).mp this
    linarith only [m_sub_n_pos]
  /-
  Consider the equation with $a=2$ and rewrite its left-hand side as a difference of squares:  $$ \frac{1}{4}\left(\left(m^{2}+n+n^{2}+m\right)^{2}-\left(m^{2}+n-n^{2}-m\right)^{2}\right)=2(m-n)^{3} $$
  -/
  have eq0: (m^2 + n + n^2 + m)^2 - (m^2 + n - n^2 - m)^2 = 8 * (m - n)^3 := by
    linarith
  /-
  Since $m^{2}+n-n^{2}-m=(m-n)(m+n-1)$, we can further reformulate the equation as  $$ \left(m^{2}+n+n^{2}+m\right)^{2}=(m-n)^{2}\left(8(m-n)+(m+n-1)^{2}\right) . $$
  -/
  have eq1: (m^2 + n + n^2 + m)^2 = (m - n)^2 * (8 * (m-n) + (m+n-1)^2) := by
    linarith
  -- show that $(m - n)^2$ divides $(m^2 + n + n^2 + m)^2$
  have : (m-n)^2 ∣ (m^2 + n + n^2 + m)^2 := by
    use 8 * (m-n) + (m+n-1)^2
  -- show that $m - n$ divides $(m^2 + n + n^2 + m)$
  have hdvd: (m-n) ∣ (m^2 + n + n^2 + m) := by
    apply (Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp
    exact this
  /-
  It follows that $8(m-n)+(m+n-1)^{2}$ is a perfect square.
  -/
  -- use `eq1` and `hdvd` to construct a integer $s$ such that $s^2 = 8 * (m - n) + (m + n - 1) ^ 2$
  have : ∃ s, s^2 = 8 * (m-n) + (m+n-1)^2 := by
    rcases hdvd with ⟨s, hs⟩
    use s
    have : (m-n)^2 * s^2 = (m-n)^2 * (8 * (m - n) + (m + n - 1) ^ 2) := by
      conv => left; rw [← mul_pow]; rw[← hs]
      exact eq1
    have l1 : (m - n)^2 ≠ 0 := by
      intro hmn; simp at hmn
      linarith
    exact mul_left_cancel₀ l1 this
  rcases this with ⟨x, hx1⟩
  /-
  Clearly $m>n$, hence there is an integer $s \geq 1$ such that  $$ (m+n-1+2 s)^{2}=8(m-n)+(m+n-1)^{2} . $$
  Subtracting the squares gives $s(m+n-1+s)=2(m-n)$. Since $m+n-1+s>m-n$, we conclude that $s<2$. Therefore the only possibility is $s=1$ and $m=3 n$.
  -/
  have : x^2 > (m + n - 1)^2 := by rw [hx1]; linarith
  have : |x| > m + n - 1 := by
    have : |x| > |m + n - 1| := by
      apply sq_lt_sq.mp
      exact this
    apply lt_of_abs_lt
    exact this
  -- then substitute $|x|$ by $ss + (m + n - 1)$ where $ss = x - (m + n - 1)$
  let ss := |x| - (m + n - 1)
  have : |x| = ss + (m + n - 1) := by rw [sub_add_cancel]
  have tpos: ss > 0 := by linarith
  -- substitute $|x|$ by $ss + (m + n - 1)$ in the equation, and simplify
  have : x^2 = (ss + (m + n - 1))^2 := by rw [← this]; simp
  rw [this] at hx1
  have l2: ss * (2*(m+n-1) + ss) = 8 * (m - n) := by linarith
  -- show that $ss$ is even by analyzing the equation
  have : Even ss := by
    apply (congrArg Even) at l2
    simp at l2
    have e1 := l2.mpr (by apply Even.mul_right; trivial)
    rw [mul_add] at e1
    have e2: Even (ss * (2 * (m + n - 1))) := by
      apply Even.mul_left; apply Even.mul_right; trivial
    have e3 := Even.sub e1 e2
    simp at e3
    apply Int.even_mul.mp at e3
    simp at e3; exact e3
  -- inequality tricks to show that $8 * (m - n) > ss * (2 * (m + n - 1))$, which constraints t to be small
  have : 8 * (m - n) > ss * (2 * (m + n - 1)) := by
    linarith [(pow_pos tpos 2)]
  -- show that $ss < 4$ by analyzing the inequality
  have : ¬ (ss ≥ 4) := by
    intro ht
    have : 2 * (m + n - 1) > 0 := by
      linarith
    have : ss * (2 * (m + n - 1)) ≥ 4 * (2 * (m + n - 1)) := by
      exact (Int.mul_le_mul_iff_of_pos_right this).mpr ht
    linarith
  simp at this

  have : ss = 2 := by
    have evenss: Even ss.natAbs := by simp; assumption
    have teq: ss.natAbs = ss := by simp; linarith
    have : ss.natAbs < 4 := by
      apply Int.ofNat_lt.mp
      rw [teq]; simp; assumption
    -- then use `fin_cases` tactic to show that $ss$ can only be $0$, $1$, $2$, or $3$
    have lemm (p : Fin 4) : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 := by
      fin_cases p; all_goals simp
    have tmap := lemm ⟨ss.natAbs, this⟩
    simp at tmap
    -- finish the proof by enumerating the possibilities
    rcases tmap with h0 | h | h | h
    · linarith
    · rw [h] at evenss; contradiction
    · rw [← teq, h]; trivial
    · rw [h] at evenss; contradiction
  /-
  However then the left-hand side of the given equation (with $a=2$ ) is greater than $m^{3}=27 n^{3}$, whereas its right-hand side equals $16 n^{3}$. The contradiction proves that $a=2$ is not friendly.
  -/
  rw [this] at l2
  -- for $t = 2$, show that the equation leads to a contradiction
  -- simplify `l2` to show $m = 3n$
  have : m = 3 * n := by linarith
  -- use the relation $m=3n$ to simplify the original equation
  rw [this] at h
  have : ((3 * n) ^ 2 + n) * (n ^ 2 + 3 * n) = 16 * n ^ 3 := by linarith
  have l3: n ^ 3 > 0 := by apply pow_pos hn 3
  -- use inequality tricks to lower down the equation's left hand side to $27 * n ^ 3$
  -- the right hand side of equation is $16 * n ^ 3$, which leads to a contradiction
  have l4: 16 * n ^ 3 > 27 * n ^ 3 := by
    rw [← this]
    linarith only [pow_pos hn 2, pow_pos hn 4, l3]
  linarith only [l3, l4]
